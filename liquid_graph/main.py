import re
import subprocess
import sys

from graphviz import Digraph

BINARY = "./_build/default/liquid_graph.exe"

KIND_STYLE = {
    "exp": ("box", "#c6d8f5"),
    "var": ("box", "#c5e0b4"),
    "ast": ("box", "#ffc000"),
    "type": ("ellipse", "#ffff99"),
    "ref": ("ellipse", "#e2c4e5"),
    "op": ("diamond", "#f4cccc"),
}

EDGE_COLOR = {
    "exp": "#000000",
    "type": "#4472c4",
    "ref": "#cc0000",
    "var": "#1a7a1a",
}


def get_raw_output(filename):
    try:
        result = subprocess.run(
            [BINARY, "api", filename], capture_output=True, text=True, check=True
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print("Error running binary:", e.stderr)
        return None


def parse_output(text):
    nodes = {}
    edges = []
    mode = None

    # Matches:  [Kind: exp] ID: flat Label: flat
    node_re = re.compile(r"^(\S+)\tID:(\S+)\tLabel:(.*)$")
    # Matches:  flat -> nu_t_flat [var]
    edge_re = re.compile(r"^(\S+)\s+->\s+(\S+)\s+\[(\S+)\]$")

    for raw in text.splitlines():
        line = raw.strip()
        if line == "--- Nodes ---":
            mode = "nodes"
            continue
        elif line == "--- Edges ---":
            mode = "edges"
            continue
        elif not line or line == "SEMANTIC FLOW GRAPH":
            continue
        elif not line or line.startswith("===") or line == "SEMANTIC FLOW GRAPH":
            continue

        if mode == "nodes":
            m = node_re.match(line)
            if m:
                kind, nid, label = m.group(1), m.group(2), m.group(3).strip()
                nodes[nid] = {"kind": kind, "label": label}
            else:
                print(f"  [WARN] unmatched node line: {line!r}", file=sys.stderr)

        elif mode == "edges":
            m = edge_re.match(line)
            if m:
                edges.append((m.group(1), m.group(2), m.group(3)))
            else:
                print(f"  [WARN] unmatched edge line: {line!r}", file=sys.stderr)

    return nodes, edges


def sanitize_id(s):
    return re.sub(r"[^a-zA-Z0-9_]", "_", s)


def pretty_label(label):
    if label.startswith("phi_nu_t_"):
        return "phi_nu_t_" + label[9:]
    if label.startswith("phi_nu_"):
        return "phi_nu_" + label[7:]
    if label.startswith("phi_"):
        return "phi_" + label[4:]
    if label.startswith("nu_t_"):
        return "nu_t_" + label[5:]
    if label.startswith("nu_"):
        return "nu_" + label[3:]
    if label.startswith("tvar_"):
        return "a_" + label[5:]
    return label or "_"


def build_graph(nodes, edges):
    dot = Digraph(format="png")
    dot.attr(rankdir="BT")
    dot.attr("node", fontname="Helvetica", fontsize="10")

    id_map = {nid: sanitize_id(nid) for nid in nodes}

    for nid, data in nodes.items():
        kind = data["kind"]
        label = pretty_label(data["label"])
        safe = id_map[nid]
        shape, color = KIND_STYLE.get(kind, ("box", "#ffffff"))
        dot.node(safe, label=label, shape=shape, fillcolor=color, style="filled")

    for src, dst, kind in edges:
        s = id_map.get(src, sanitize_id(src))
        d = id_map.get(dst, sanitize_id(dst))
        color = EDGE_COLOR.get(kind, "#000000")
        dot.edge(s, d, color=color, penwidth="1.5")

    return dot


def main():
    if len(sys.argv) < 2:
        print("Usage: python main.py <file.ml> [plot|code|debug]")
        return

    filename = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 else "plot"

    raw = get_raw_output(filename)
    if raw is None:
        return

    if mode == "debug":
        print("=== RAW OUTPUT ===")
        print(raw[:2000])
        return

    nodes, edges = parse_output(raw)
    print(f"Parsed {len(nodes)} nodes, {len(edges)} edges", file=sys.stderr)

    if not nodes:
        print("No nodes parsed — run with 'debug' to inspect raw output.")
        return

    dot = build_graph(nodes, edges)
    if mode == "code":
        print(dot.source)
    else:
        dot.render("flowchart", view=True)


if __name__ == "__main__":
    main()
