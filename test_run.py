import networkx as nx
import torch
from torch_geometric.data import Data

from GNN_encoder.encoder import gnn_encoder
from liquid_graph.parser import get_ocaml_tokenizer, parse

code = """
let max x y = if x > y then x else y
"""

parser = get_ocaml_tokenizer()
token_list = parse(parser, code)

G = nx.DiGraph()

vocab = {}
next_vocab_id = 0

for i, token in enumerate(token_list):
    token_text = token[0]
    token_type = token[1]

    if token_text not in vocab:
        vocab[token_text] = next_vocab_id
        next_vocab_id += 1

    emb_id = vocab[token_text]
    G.add_node(i, text=token_text, type=token_type, emb_id=emb_id)

for i in range(len(token_list) - 1):
    G.add_edge(i, i + 1, edge_type="next")

sorted_nodes = sorted(G.nodes(data=True))
x = torch.tensor([data["emb_id"] for _, data in sorted_nodes], dtype=torch.long)
sorted_nodes = sorted(G.nodes(data=True))
x = torch.tensor([data["emb_id"] for _, data in sorted_nodes], dtype=torch.long)

edge_index = list()
type_mapping = {"next": 0}
edge_type_list = list()
for u, v, data in G.edges(data=True):
    edge_index.append([u, v])
    type_str = data["edge_type"]
    type_id = type_mapping[type_str]
    edge_type_list.append(type_id)

edge_type_tensor = torch.tensor(edge_type_list, dtype=torch.long)

edge_index = torch.tensor(edge_index, dtype=torch.long).t().contiguous()

graph_data = Data(x=x, edge_index=edge_index)
gnn = gnn_encoder(10, 64, 1, 0)
print(graph_data.x.shape)
print(gnn(graph_data.x, graph_data.edge_index, edge_type_tensor))
