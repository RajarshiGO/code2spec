import re
import subprocess
import sys

import torch

from liquid_graph.graph_processor import GraphNode, GraphPreprocessor

BINARY = "../Liquid_Graph/_build/default/liquid_graph.exe"
NODE_TYPE_MAP = {"var": 0, "op": 1, "exp": 2, "type": 3, "ref": 4, "ast": 5, "lit": 6}
EDGE_TYPE_MAP = {"exp": 0, "type": 1, "ref": 2, "var": 3}

GLOBAL_NODE_VOCAB = {"PAD": 0, "UNK": 1}
_next_id = [2]


def get_node_id(token):
    if token not in GLOBAL_NODE_VOCAB:
        GLOBAL_NODE_VOCAB[token] = _next_id[0]
        _next_id[0] += 1
    return GLOBAL_NODE_VOCAB[token]


def get_raw_output(filename):
    r = subprocess.run(
        [BINARY, "api", filename], capture_output=True, text=True, check=True
    )
    return r.stdout


def parse_output(text):
    nodes, edges, mode = {}, [], None
    # NEW: matches "var\tID:x\tLabel:x"
    node_re = re.compile(r"^(\S+)\tID:(\S+)\tLabel:(.*)$")
    edge_re = re.compile(r"(\S+)\s+->\s+(\S+)\s+\[(\S+)\]")
    for raw in text.splitlines():
        line = raw.strip()
        if line == "--- Nodes ---":
            mode = "nodes"
            continue
        elif line == "--- Edges ---":
            mode = "edges"
            continue
        elif not line or "SEMANTIC" in line or line.startswith("[AST]"):
            continue
        if mode == "nodes":
            m = node_re.match(line)
            if m:
                nodes[m.group(2)] = {"kind": m.group(1), "label": m.group(3).strip()}
        elif mode == "edges":
            m = edge_re.match(line)
            if m:
                edges.append((m.group(1), m.group(2), m.group(3)))
    return nodes, edges


def normalize_type(label):
    """Map OCaml type labels to grammar type keys."""
    if label in ("int", "bool", "list", "tree", "bst"):
        return label
    if label.startswith("'"):  # 'a, 'b, etc. → int (all our measures are int-valued)
        return "int"
    for known in ("list", "tree"):
        if known in label.lower():
            return known
    return "int"  # unknown primitive → int


def extract_base_types(nodes_dict, edges_list):
    base_type = {}
    for src_id, dst_id, kind in edges_list:
        if kind != "type":
            continue
        src = nodes_dict.get(src_id, {})
        dst = nodes_dict.get(dst_id, {})
        if dst.get("kind") == "type":
            base_type[src_id] = normalize_type(dst.get("label", "unknown"))
        elif src.get("kind") == "type":
            base_type[dst_id] = normalize_type(src.get("label", "unknown"))
    return base_type


def extract_refinement_contexts(
    nodes_dict, edges_list, nid_to_idx, sorted_nodes, nid_to_type
):
    fn_output_nus = {nid for nid in nodes_dict if nid.startswith("nu_t_")}
    param_of_fn = {}
    for src, dst, kind in edges_list:
        if (
            kind == "var"
            and nodes_dict.get(src, {}).get("kind") == "var"
            and nodes_dict.get(dst, {}).get("kind") == "exp"
        ):
            param_of_fn.setdefault(dst, []).append(src)
    nu_to_fn = {
        dst: src
        for src, dst, kind in edges_list
        if kind == "var" and dst in fn_output_nus
    }
    nu_to_phi = {
        src: dst
        for src, dst, kind in edges_list
        if kind == "ref" and src in fn_output_nus
    }
    nid_to_sorted = {
        nid: new_idx
        for new_idx, node in enumerate(sorted_nodes)
        for nid, idx in nid_to_idx.items()
        if node.id == idx
    }
    contexts = {}
    for nu_nid in fn_output_nus:
        if nu_nid not in nu_to_phi:
            continue
        fn_nid = nu_to_fn.get(nu_nid)
        params = param_of_fn.get(fn_nid, [])
        typed = {}
        for cnid in params + [nu_nid]:
            sidx = nid_to_sorted.get(cnid)
            if sidx is None:
                continue
            tstr = nid_to_type.get(cnid, "unknown")
            name = nodes_dict[cnid]["label"]
            if cnid == nu_nid:  # bound variable → always "v"
                name = "v"
            typed.setdefault(tstr, []).append((sidx, name))
            if tstr != "unknown":
                typed.setdefault("unknown", []).append((sidx, name))
        contexts[nu_nid] = {
            "nu_sorted_idx": nid_to_sorted.get(nu_nid),
            "phi_nid": nu_to_phi[nu_nid],
            "fn_label": nodes_dict.get(fn_nid, {}).get("label", "?"),
            "nu_type": nid_to_type.get(nu_nid, "unknown"),
            "typed": typed,
        }
    return contexts


def to_gnn_tensors(filename):
    nodes_dict, edges_list = parse_output(get_raw_output(filename))
    nid_to_type = extract_base_types(nodes_dict, edges_list)
    constants = [
        {"nid": nid, "label": data["label"]}
        for nid, data in nodes_dict.items()
        if data["kind"] == "lit"
    ]
    raw_nodes, nid_to_idx = [], {}
    for idx, (nid, data) in enumerate(nodes_dict.items()):
        node = GraphNode(idx, data["kind"], data["label"])
        node.emb_id = get_node_id(data["label"])
        raw_nodes.append(node)
        nid_to_idx[nid] = idx
    raw_edges, edge_type_lookup = [], {}
    for src_id, dst_id, kind in edges_list:
        if src_id in nid_to_idx and dst_id in nid_to_idx:
            s, d = nid_to_idx[src_id], nid_to_idx[dst_id]
            raw_edges.append((s, d))
            edge_type_lookup[(s, d)] = EDGE_TYPE_MAP.get(kind, 0)
    pp = GraphPreprocessor(raw_nodes, raw_edges)
    sorted_nodes, new_edges, _, _, _ = pp.process()
    x = torch.tensor([n.emb_id for n in sorted_nodes], dtype=torch.long)
    node_type = torch.tensor(
        [NODE_TYPE_MAP.get(n.node_type, 5) for n in sorted_nodes], dtype=torch.long
    )
    if new_edges:
        new_to_old = {i: node.id for i, node in enumerate(sorted_nodes)}
        etypes = [
            edge_type_lookup[(new_to_old[u], new_to_old[v])] for u, v in new_edges
        ]
        edge_index = torch.tensor(new_edges, dtype=torch.long).t().contiguous()
        edge_type_tensor = torch.tensor(etypes, dtype=torch.long)
    else:
        edge_index = torch.zeros(2, 0, dtype=torch.long)
        edge_type_tensor = torch.zeros(0, dtype=torch.long)
    ref_contexts = extract_refinement_contexts(
        nodes_dict, edges_list, nid_to_idx, sorted_nodes, nid_to_type
    )
    return (
        x,
        edge_index,
        edge_type_tensor,
        node_type,
        sorted_nodes,
        ref_contexts,
        constants,
    )
