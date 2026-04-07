import torch
import torch.nn as nn

from GNN_encoder.gnn_layer import graphOP


class gnn_encoder(nn.Module):
    def __init__(
        self,
        vocab_size,
        hidden_dim,
        num_edge_types,
        num_node_types,
        heads=1,
        pretrained_embeddings=None,
    ):
        super().__init__()

        self.node_embedding = nn.Embedding(vocab_size, hidden_dim)

        if pretrained_embeddings is not None:
            self.node_embedding.weight.data.copy_(pretrained_embeddings)

        self.msg_op = graphOP(
            hidden_dim=hidden_dim,
            num_edge_types=num_edge_types,
            heads=heads,
            num_node_types=num_node_types,
        )

        self.gru = nn.GRUCell(hidden_dim, hidden_dim)

    def forward(self, x, edge_index, edge_type, node_type):
        """
        x:         [num_nodes]
        edge_index:[2, num_edges]
        edge_type: [num_edges]
        node_type: [num_nodes]
        """
        h = self.node_embedding(x)

        for _ in range(5):
            aggr_message = self.msg_op(h, edge_index, edge_type, node_type)

            h = self.gru(aggr_message, h)

        return h
