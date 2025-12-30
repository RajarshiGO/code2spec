import torch
import torch.nn as nn

from GNN_encoder.gnn_layer import graphOP


class gnn_encoder(nn.Module):
    def __init__(
        self,
        vocab_size,
        hidden_dim,
        num_edge_types,
        num_known_types,
        pretrained_embeddings=None,
    ):
        super(gnn_encoder, self).__init__()

        self.node_embedding = nn.Embedding(vocab_size, hidden_dim)  # etc...
        self.node_embedding = nn.Embedding(vocab_size, hidden_dim)  # etc...
        self.msg_op = graphOP(hidden_dim, num_edge_types)
        self.gru = nn.GRUCell(hidden_dim, hidden_dim)
        self.num_edge_types = num_edge_types

    def forward(self, x, edge_index, edge_type):
        h = self.node_embedding(x)

        for step in range(5):
            aggr_message = self.msg_op(h, edge_index, edge_type)
            h = self.gru(aggr_message, h)

        return h
