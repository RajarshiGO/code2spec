import re

import torch
import torch.nn as nn
import torch.nn.functional as F

from decoder.pos_encode import TreePosEncode
from decoder.ruleset import ADT_SPECS, build_ruleset


class Node:
    def __init__(self, rule=None, name=None, lg_node=None):
        self.rule = rule
        self.name = name
        self.lg_node = lg_node
        self.children = []

    def add_child(self, node):
        self.children.append(node)

    def _to_inner_str(self):
        """Recursive helper that builds the string WITHOUT adding quantifiers."""
        # 1. Leaf Nodes
        if not self.children:
            return str(self.name) if self.name is not None else str(self.rule)

        # 2. Phase 2: Logical Operators (Clean, no parentheses)
        if self.name in ["&&", "||"] and len(self.children) == 2:
            return f"{self.children[0]._to_inner_str()} {self.name} {self.children[1]._to_inner_str()}"

        # 3. Phase 3: Predicate Grammar (P -> I op_int I)
        if len(self.children) == 3:
            return f"{self.children[0]._to_inner_str()} {self.children[1]._to_inner_str()} {self.children[2]._to_inner_str()}"

        # 4. Pass-through nodes (e.g., 'I' just holding 'var_int' or 'const')
        if len(self.children) == 1:
            return self.children[0]._to_inner_str()

        # 5. Safe Fallback
        return " ".join([c._to_inner_str() for c in self.children])

    def __repr__(self):
        """Top-level wrapper that implicitly quantifies the final string."""
        raw_spec = self._to_inner_str()

        # If any membership predicate is found anywhere in the tree,
        # add the quantifier to the absolute front.
        if "mem_" in raw_spec:
            # Search for which qvar candidate was actually used in the string
            for candidate in ["u", "w", "z", "y"]:
                # \b checks for a "word boundary" so it matches the exact standalone variable
                if re.search(rf"\b{candidate}\b", raw_spec):
                    return f"forall {candidate}, {raw_spec}"

            # Safe fallback just in case
            return f"forall y, {raw_spec}"

        return raw_spec


def weights_init(m):
    classname = m.__class__.__name__
    if classname.find("Linear") != -1:
        nn.init.xavier_uniform_(m.weight)
        if m.bias is not None:
            nn.init.constant_(m.bias, 0.0)
    elif classname.find("GRU") != -1:
        for name, param in m.named_parameters():
            if "weight" in name:
                nn.init.xavier_uniform_(param)
            elif "bias" in name:
                nn.init.constant_(param, 0.0)


class TransformerDecoder(nn.Module):
    def __init__(self, latent_dim, num_heads=4, num_layers=8, dropout=0.2):
        super(TransformerDecoder, self).__init__()
        self.d_model = latent_dim
        self.device = "cuda" if torch.cuda.is_available() else "cpu"
        self.max_depth = 5
        self.vocab_size = 100

        self.fixed_vocab_embed = nn.Embedding(self.vocab_size, latent_dim)
        self.node_proj = nn.Linear(latent_dim, latent_dim)
        self.pos_encoder = TreePosEncode(latent_dim, max_branch=3)
        self.bos_embed = nn.Parameter(torch.zeros(1, latent_dim))

        decoder_layer = nn.TransformerDecoderLayer(
            d_model=latent_dim, nhead=num_heads, dropout=dropout
        )
        self.transformer = nn.TransformerDecoder(decoder_layer, num_layers=num_layers)

        self.structure_head = nn.Linear(latent_dim, 3)

        self.grammar_key_proj = nn.Linear(latent_dim, latent_dim)
        nn.init.xavier_uniform_(self.grammar_key_proj.weight)

        self.pointer_query_proj = nn.Linear(latent_dim, latent_dim)
        self.pointer_key_proj = nn.Linear(latent_dim, latent_dim)
        self.attn_scale = latent_dim**0.5
        nn.init.xavier_uniform_(self.pointer_query_proj.weight)
        nn.init.xavier_uniform_(self.pointer_key_proj.weight)

        self.value_head = nn.Sequential(
            nn.Linear(latent_dim, latent_dim),
            nn.LayerNorm(latent_dim),
            nn.ReLU(),
            nn.Linear(latent_dim, latent_dim // 2),
            nn.ReLU(),
            nn.Linear(latent_dim // 2, 1),
        )

        self.rule_to_idx = {}
        self._build_full_rule_mapping()
        self.current_prompt_idx = None
        self.active_ruleset = {}
        self.arg_typed = {}
        self.nll = 0.0
        self.root = None

    def _build_full_rule_mapping(self):
        """Build idx map over all possible ADT types so embeddings are stable."""
        all_typed = {t: [(0, "v")] for t in ADT_SPECS}
        all_typed.update({"int": [(0, "v")], "bool": [(0, "v")]})
        maximal = build_ruleset(all_typed)
        idx = 1
        for key, prods in maximal.items():
            if key not in self.rule_to_idx:
                self.rule_to_idx[key] = idx
                idx += 1
            for prod in prods:
                s = str(prod)
                if s not in self.rule_to_idx:
                    self.rule_to_idx[s] = idx
                    idx += 1

    def _get_idx(self, token):
        if token not in self.rule_to_idx:
            self.rule_to_idx[token] = len(self.rule_to_idx) + 1
        raw = self.rule_to_idx[token]
        return raw if raw < self.vocab_size else self.vocab_size - 1

    def _get_node_embedding(self, n, program_ctx):
        if n.lg_node is not None:
            try:
                node_idx = program_ctx.lg.node_list.index(n.lg_node)
                vec = self.cached_node_embeddings[node_idx].unsqueeze(0)
                return self.node_proj(vec)  # [1, d]
            except ValueError:
                pass
        token = n.name if n.name else str(n.rule)
        idx = self.rule_to_idx.get(token, abs(hash(token)) % self.vocab_size)
        return self.fixed_vocab_embed(torch.tensor([idx]).to(self.device))  # [1, d]

    def _process_tree(self, node, program_ctx):
        seq_vectors = []
        bos_pos = self.pos_encoder.encode_path([])
        seq_vectors.append(self.bos_embed + bos_pos.unsqueeze(0))
        if self.current_prompt_idx is not None:
            seq_vectors.append(
                self.node_proj(
                    self.cached_node_embeddings[self.current_prompt_idx].unsqueeze(0)
                )
            )
        if node is not None:
            self._traverse_tree(node, program_ctx, seq_vectors, [])
        return seq_vectors

    def _traverse_tree(self, node, program_ctx, seq_vectors, curr_path):
        if node is None:
            return
        vec = self._get_node_embedding(node, program_ctx)
        pos_enc = self.pos_encoder.encode_path(curr_path)
        seq_vectors.append(vec + pos_enc.unsqueeze(0))
        for i, child in enumerate(node.children):
            self._traverse_tree(child, program_ctx, seq_vectors, curr_path + [i])

    def transformer_step(self, history):
        x = torch.cat(history, dim=0).unsqueeze(1)
        sz = x.size(0)
        tgt_mask = nn.Transformer.generate_square_subsequent_mask(sz).to(self.device)
        memory = self.cached_node_embeddings.unsqueeze(1)
        output = self.transformer(x, memory, tgt_mask=tgt_mask)
        return output[-1, 0, :]

    def choose_action(
        self, state, cls_w, use_random, eps, is_pointer_task=False, mask=None
    ):
        if state.dim() == 1:
            state = state.unsqueeze(0)
        if is_pointer_task:
            logits = (
                torch.mm(
                    self.pointer_query_proj(state), self.pointer_key_proj(cls_w).t()
                )
                / self.attn_scale
            )
        elif isinstance(cls_w, torch.Tensor):
            logits = torch.mm(state, self.grammar_key_proj(cls_w).t()) / self.attn_scale
        elif isinstance(cls_w, nn.Linear):
            logits = cls_w(state)
        else:
            raise ValueError("Unknown cls_w type")
        if mask is not None:
            logits = logits.masked_fill(mask, float("-inf"))
        ll = F.log_softmax(logits, dim=1)
        if use_random:
            probs = torch.exp(ll)
            uprob = eps / max(1, logits.shape[1])
            scores = probs * (1 - eps) + uprob
            if mask is not None:
                scores = scores.masked_fill(mask, 0.0)
            try:
                picked = torch.multinomial(scores, 1)
            except RuntimeError:
                picked = torch.argmax(ll, dim=1).unsqueeze(0)
        else:
            _, picked = torch.max(ll, 1)
            picked = picked.unsqueeze(0)
        picked = picked.view(-1)
        self.nll += F.nll_loss(ll, picked)
        return picked.item()

    def updateTree(self, program_ctx, node, use_random, eps, depth=0):
        symbol = str(node.rule).strip()

        if self.root:
            hist = self._process_tree(self.root, program_ctx)
            state = self.transformer_step(hist)
        else:
            state = torch.zeros(1, self.d_model, device=self.device)

        # ── PHASE 1: POINTERS ─────────────────────────────────────────────────
        # Typed variable pointer — handles var_int, var_list, var_tree, etc.
        if symbol.startswith("var_"):
            type_key = symbol[4:]
            candidates = self.arg_typed.get(type_key, [])
            if not candidates:
                node.name = "v"
                return node
            idxs = [s for s, _ in candidates]
            names = [n for _, n in candidates]
            c_embeds = self.cached_node_embeddings.index_select(
                0, torch.tensor(idxs, device=self.device)
            )
            picked = self.choose_action(
                state, c_embeds, use_random, eps, is_pointer_task=True
            )
            node.name = names[picked]
            node.lg_node = idxs[picked]
            return node

        # Constant pointer
        if symbol == "const":
            raw_consts = getattr(program_ctx, "constants", []) or [0]
            candidates = [str(c) for c in raw_consts]
            base = getattr(program_ctx, "const_start_idx", 0)
            idxs = [base + i for i in range(len(candidates))]
            max_idx = self.cached_node_embeddings.shape[0] - 1
            safe_idxs = [min(i, max_idx) for i in idxs]
            c_embeds = self.cached_node_embeddings.index_select(
                0, torch.tensor(safe_idxs, device=self.device)
            )
            picked = self.choose_action(
                state, c_embeds, use_random, eps, is_pointer_task=True
            )
            node.name = candidates[picked]
            return node

        # ── PHASE 2: STRUCTURE ────────────────────────────────────────────────
        elif symbol == "S":
            mask = None
            if depth >= self.max_depth - 1:
                mask = torch.zeros(1, 3, dtype=torch.bool, device=self.device)
                mask[0, 1] = True
                mask[0, 2] = True
            action = self.choose_action(
                state, self.structure_head, use_random, eps, mask=mask
            )
            if action == 0:
                node.rule = "P"
                return self.updateTree(program_ctx, node, use_random, eps, depth)
            node.name = "&&" if action == 1 else "||"
            node.children = []
            node.add_child(Node("S", lg_node=node.lg_node))
            node.add_child(Node("S", lg_node=node.lg_node))
            for c in node.children:
                self.updateTree(program_ctx, c, use_random, eps, depth + 1)
            return node

        # ── PHASE 3: GRAMMAR ──────────────────────────────────────────────────
        if symbol in self.active_ruleset:
            productions = self.active_ruleset[symbol]
            mask = None

            if symbol == "I":
                mask = torch.zeros(
                    1, len(productions), dtype=torch.bool, device=self.device
                )
                # mask const if no constants in scope
                if not getattr(program_ctx, "constants", []) and "const" in productions:
                    mask[0, productions.index("const")] = True
                # mask recursive oparith near depth limit
                if depth >= self.max_depth - 2:
                    for i, p in enumerate(productions):
                        if p == ("I", "oparith", "I"):
                            mask[0, i] = True
                if not mask.any():
                    mask = None

            prod_embeds = [
                self.fixed_vocab_embed(
                    torch.tensor([self._get_idx(str(p))]).to(self.device)
                )
                for p in productions
            ]
            prod_tensor = torch.stack(prod_embeds).squeeze(1)
            rule_idx = self.choose_action(
                state, prod_tensor, use_random, eps, mask=mask
            )
            selected = productions[rule_idx]
            tokens = [selected] if isinstance(selected, str) else list(selected)
            for token in tokens:
                child = Node(rule=token)
                tc = str(token).strip()
                if tc.startswith("var_") or tc == "const" or tc in self.active_ruleset:
                    node.add_child(child)
                    self.updateTree(program_ctx, child, use_random, eps, depth + 1)
                else:
                    child.name = token
                    node.add_child(child)
            return node

        if not node.name:
            node.name = symbol
        return node

    def forward(
        self,
        program_ctx,
        node_embedding,
        use_random,
        eps=0.05,
        target_var_idx=None,
        arg_typed=None,
    ):
        self.cached_node_embeddings = node_embedding
        self.arg_typed = arg_typed or {}
        self.active_ruleset = build_ruleset(self.arg_typed)
        # print("=" * 50)
        # print(self.active_ruleset)
        # print(self.arg_typed)
        # print("=" * 50)
        self.nll = 0.0
        self.current_prompt_idx = target_var_idx

        initial_history = self._process_tree(None, program_ctx)
        initial_state = self.transformer_step(initial_history)
        est = self.value_head(initial_state).squeeze()  # scalar for mse_loss

        self.root = Node(rule="S", name=None)
        self.root = self.updateTree(program_ctx, self.root, use_random, eps)
        return self.root, self.nll, est
