import json
import os
import re
import subprocess
import sys
from collections import deque

import torch
import torch.nn.functional as F
import torch.optim as optim
from decoder.decoder3 import Node, TransformerDecoder
from z3 import *

from GNN_encoder.encoder import gnn_encoder

# Dynamic graph building and processing
from liquid_graph.build_graph import to_gnn_tensors
from liquid_graph.graph_processor import ProgramContext

# Fast OCaml evaluator
from utils.evaluator import SpecEvaluator, check_all_cexs


def parse_smt_cex(cex_str):
    if not cex_str:
        return {}
    pattern = r"\(define-fun\s+(\w+)\s+\(\)\s+Int\s+(-?\d+)\)"
    matches = re.findall(pattern, cex_str)
    return {name: int(val) for name, val in matches} if matches else {}


# ── Reward engine ─────────────────────────────────────────────────────────────
def parse_adt_string(s):
    """
    Generically parses ANY Algebraic Data Type string into clean JSON.
    """
    if not isinstance(s, str):
        return s

    s = re.sub(r"([a-zA-Z_]\w*)\s*\(", r"(\1 ", s)
    s = s.replace("(", " ( ").replace(")", " ) ").replace(",", " ")
    tokens = [t for t in s.split() if t]

    def walk():
        if not tokens:
            return None
        t = tokens.pop(0)

        if t == "(":
            sub = []
            while tokens and tokens[0] != ")":
                sub.append(walk())
            if tokens:
                tokens.pop(0)

            if not sub:
                return {"variant": "Unit", "args": []}

            head = sub[0]
            tag = (
                head["variant"]
                if isinstance(head, dict) and "variant" in head
                else str(head)
            )
            return {"variant": tag, "args": sub[1:]}
        else:
            try:
                return int(t)
            except ValueError:
                if t.lower() == "true":
                    return True
                if t.lower() == "false":
                    return False
                if t.startswith('"') and t.endswith('"'):
                    return t.strip('"')
                return {"variant": t, "args": []}

    parsed = walk()
    return parsed if parsed is not None else s


class RewardEngine:
    def __init__(self, verifier_path):
        self.verifier = verifier_path

    def verify_and_get_feedback(self, spec_string: str, ocaml_file_path: str):
        # print(spec_string)
        try:
            result = subprocess.run(
                [self.verifier, spec_string, ocaml_file_path],
                capture_output=True,
                text=True,
            )
            output = result.stdout.strip()
            output_flat = output.replace("\n", " ")
            clean = re.sub(r"- (\d)", r"-\1", output_flat)

            data = None
            try:
                si = clean.find("{")
                ei = clean.rfind("}")
                if si != -1 and ei != -1:
                    data = json.loads(clean[si : ei + 1])
            except json.JSONDecodeError as e:
                print(f"JSON error: {e}")
                data = None

            if data is None:
                print(f"Raw output: {output}")
                return -1.0, {}

            status = data.get("status", "error")
            sub_spec_score_str = data.get("sub_spec_score", "0/1")
            try:
                num_str, den_str = sub_spec_score_str.split("/")
                partial_reward = (
                    float(num_str) / float(den_str) if float(den_str) != 0 else -1.0
                )
            except Exception:
                partial_reward = -1.0

            if status == "valid":
                return 1.0, {}
            elif status == "invalid":
                raw_cex = data.get("cex", {})
                parsed_cex = {}

                if isinstance(raw_cex, dict):
                    for var, val in raw_cex.items():
                        parsed_cex[var] = parse_adt_string(val)

                return partial_reward, parsed_cex

            # ---> THE FIX IS HERE <---
            # If status is "error", "timeout", or anything else, fallback to penalty
            return -1.0, {}

        except Exception as e:
            import traceback

            print(f"Verifier error: {e}")
            traceback.print_exc()
            return -1.0, {}


# ── Trivial spec check ────────────────────────────────────────────────────────


def is_trivial(code_str, program_ctx):
    # Extract variable names natively from the program context
    var_names = [v.name for v in program_ctx.lg.variables]

    if not any(v in code_str for v in var_names):
        return True
    inner = code_str.strip().strip("()")
    for op in ["==", "=", "!="]:
        if op in inner:
            parts = inner.split(op)
            if len(parts) == 2 and parts[0].strip() == parts[1].strip():
                return True
    return False


# ── Z3 gatekeeper ────────────────────────────────────────────────────────────


class Z3Gatekeeper:
    def check_triviality(self, invariant_str):
        try:
            if "forall" in invariant_str or "mem(" in invariant_str:
                return False, "valid", invariant_str

            clean = re.sub(r"len\((\w+)\)", r"\1_len", invariant_str)
            clean = re.sub(r"size\((\w+)\)", r"\1_size", clean)
            clean = re.sub(r"height\((\w+)\)", r"\1_height", clean)
            clean = re.sub(r"hd\((\w+)\)", r"\1_hd", clean)

            clean = clean.replace(">=", "GE").replace("<=", "LE").replace("!=", "NEQ")
            clean = clean.replace("=", "==")
            clean = clean.replace("GE", ">=").replace("LE", "<=").replace("NEQ", "!=")

            clean = clean.replace("∧", " and ").replace("∨", " or ")
            clean = clean.replace("&&", " and ").replace("||", " or ")
            clean = clean.replace("true", "True").replace("false", "False")

            tokens = re.findall(r"[a-zA-Z_]\w*", clean)
            keywords = {"and", "or", "True", "False", "not"}
            z3_vars = {t: Int(t) for t in tokens if t not in keywords}

            expr = eval(clean, {}, z3_vars)

            if not is_bool(expr):
                return True, "type_mismatch", str(expr)
            if is_true(simplify(expr)):
                return True, "trivial_true", str(expr)
            if is_false(simplify(expr)):
                return True, "trivial_false", str(expr)

            simp = simplify(expr)

            if len(invariant_str) > 20 and len(str(simp)) < len(invariant_str) * 0.6:
                return True, "bloated", str(simp)

            return False, "valid", str(simp)

        except Exception as e:
            return True, "error", str(e)


# ── One training step ─────────────────────────────────────────────────────────

running_reward_mean = 0.0


def train_one_step(
    decoder,
    gnn,
    reward_engine,
    optimizer,
    program_ctx,
    x,
    edge_index,
    edge_type,
    node_type,
    target_var_idx,
    arg_typed,
    ml_file,
    z3_checker,
    evaluator,
    step=0,
    eps=0.0,
):
    global running_reward_mean
    decoder.train()
    gnn.train()
    optimizer.zero_grad()

    node_embeddings = gnn(x, edge_index, edge_type, node_type)

    root, nll_loss, val_est = decoder(
        program_ctx,
        node_embeddings,
        use_random=True,
        eps=eps,
        target_var_idx=target_var_idx,
        arg_typed=arg_typed,
    )
    generated_code = str(root)

    # Fast evaluation check against accumulated CEXs
    passed_all, count = check_all_cexs(
        evaluator, generated_code, program_ctx.accumulated_cexs
    )

    final_reward = 0.0
    is_solved = False

    if not passed_all:
        total_cexs = max(1, len(program_ctx.accumulated_cexs))
        final_reward = count / total_cexs
    else:
        is_bad, status, _ = z3_checker.check_triviality(generated_code)
        if is_bad:
            final_reward = -1.0
        else:
            base_reward, cex = reward_engine.verify_and_get_feedback(
                generated_code, ml_file
            )
            if base_reward == 1.0 and not cex:
                final_reward = 2.0
                is_solved = True
            elif cex and isinstance(cex, dict):
                if cex not in program_ctx.accumulated_cexs:
                    program_ctx.accumulated_cexs.append(cex)
                    print(f"New CEX acquired: {cex}")
                final_reward = base_reward

    if step == 0:
        running_reward_mean = final_reward
    else:
        running_reward_mean = final_reward

    reward_t = torch.tensor(final_reward, device=decoder.device)
    advantage = reward_t - running_reward_mean
    policy_loss = nll_loss * -advantage.detach()
    value_loss = F.mse_loss(val_est.squeeze(), reward_t)
    total_loss = policy_loss + 0.5 * value_loss

    total_loss.backward()
    torch.nn.utils.clip_grad_norm_(decoder.parameters(), max_norm=0.5)
    torch.nn.utils.clip_grad_norm_(gnn.parameters(), max_norm=0.5)
    optimizer.step()

    return total_loss.item(), final_reward, generated_code, is_solved


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python train3.py <file.ml>")
        sys.exit(1)

    ml_file = sys.argv[1]
    device = "cuda" if torch.cuda.is_available() else "cpu"

    # 1. Fetch Tensors and Node lists dynamically from build_graph
    x, edge_index, edge_type, node_type, sorted_nodes, ref_contexts, raw_constants = (
        to_gnn_tensors(ml_file)
    )

    if not ref_contexts:
        print("No refinement targets found.")
        sys.exit(1)

    # 2. Bucket the sorted nodes so we can use ProgramContext
    ast_nodes = []
    variables = []
    constants = []

    for node in sorted_nodes:
        n_type = node.node_type.lower()
        if "var" in n_type:
            variables.append(node)
        elif "const" in n_type or n_type.isdigit():
            constants.append(node)
        else:
            ast_nodes.append(node)

    # 3. Initialize the external ProgramContext
    program_ctx = ProgramContext(ast_nodes, variables, constants)

    x = x.to(device)
    edge_index = edge_index.to(device)
    edge_type = edge_type.to(device)
    node_type = node_type.to(device)

    # 4. Initialize Models
    vocab_size = max(n.emb_id for n in sorted_nodes) + 2
    gnn = gnn_encoder(
        vocab_size=vocab_size,
        hidden_dim=64,
        num_edge_types=4,
        num_node_types=7,
        heads=2,
    ).to(device)
    decoder = TransformerDecoder(latent_dim=64).to(device)

    if os.path.isfile("gnn_model_weights.pth") and os.path.isfile(
        "decoder_model_weights.pth"
    ):
        gnn.load_state_dict(
            torch.load("gnn_model_weights.pth", map_location=device, weights_only=True)
        )
        decoder.load_state_dict(
            torch.load(
                "decoder_model_weights.pth", map_location=device, weights_only=True
            )
        )
        print("Loaded saved weights.")

    optimizer = optim.Adam(
        list(gnn.parameters()) + list(decoder.parameters()), lr=0.002
    )

    engine = RewardEngine("./utils/verifier/_build/default/main.exe")
    z3_checker = Z3Gatekeeper()

    # Fast OCaml evaluator initialization
    evaluator = SpecEvaluator(
        ocaml_binary_path="./utils/evaluator/_build/default/cex_eval.exe"
    )

    ctx_items = list(ref_contexts.items())
    history = list()

    print(f"Targets: {[v['fn_label'] for v in ref_contexts.values()]}")

    # 5. Training Loop
    try:
        for step in range(1000):
            # Round Robin target scheduling
            nu_nid, ctx = ctx_items[step % len(ctx_items)]
            # eps = max(0.002, 0.5 - step * 0.001)
            if step < 10:
                eps = 0.002  # 100% Random (Gather data)
            # elif step < 1000:
            #     # Decay from 1.0 to 0.1 over 900 steps
            #     eps = 1.0 - ((step - 100) / 900.0) * 0.9
            else:
                eps = 0.002

            loss, reward, code, solved = train_one_step(
                decoder,
                gnn,
                engine,
                optimizer,
                program_ctx,
                x,
                edge_index,
                edge_type,
                node_type,
                target_var_idx=ctx["nu_sorted_idx"],
                arg_typed=ctx["typed"],
                ml_file=ml_file,
                z3_checker=z3_checker,
                evaluator=evaluator,
                step=step,
                eps=eps,
            )
            history.append(reward)

            if is_trivial(code, program_ctx):
                print(f"Step {step:4d} | Trivial: {code}")
                continue

            if step % 10 == 0 or solved:
                avg = sum(list(history)[-10:]) / min(10, len(history))
                print(
                    f"Step {step:4d} | fn={ctx['fn_label']:10s} | "
                    f"AvgR={avg:.2f} | Loss={loss:.4f} | {code}"
                )

            if solved:
                print(f"\nSUCCESS at step {step}: {code}")
                torch.save(gnn.state_dict(), "gnn_model_weights.pth")
                torch.save(decoder.state_dict(), "decoder_model_weights.pth")
                break

            if step % 100 == 0 and step > 0:
                torch.save(gnn.state_dict(), "gnn_model_weights.pth")

    finally:
        # Guarantee the OCaml subprocess is terminated cleanly on exit/crash
        evaluator.close()
