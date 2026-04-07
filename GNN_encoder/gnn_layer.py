import torch
import torch.nn as nn
import torch.nn.functional as F
from torch_geometric.nn import MessagePassing
from torch_geometric.utils import softmax


class graphOP(MessagePassing):
    """
    Define message passing and aggregation operator
    """

    def __init__(self, hidden_dim, num_edge_types, heads=4, num_node_types=6):
        super(graphOP, self).__init__(aggr="add", node_dim=0)
        assert hidden_dim % heads == 0
        self.hidden_dim = hidden_dim
        self.num_edge_types = num_edge_types
        self.heads = heads
        self.head_dim = hidden_dim // heads
        self.proj = nn.ModuleList(
            [
                nn.Linear(hidden_dim, hidden_dim, bias=False)
                for _ in range(num_edge_types)
            ]
        )
        # TODO: Splitting the hidden dimension in case of multi-head attention
        self.att_vec = nn.Parameter(
            torch.Tensor(num_node_types, 1, heads, 2 * self.head_dim)
        )
        nn.init.xavier_uniform_(self.att_vec)

    def forward(self, x, edge_index, edge_type, node_type):
        """
        x:          [num_nodes, hidden_dim]
        edge_index: [2, num_edges]
        edge_type:  [num_edges]
        node_type:  [num_nodes]
        """
        all_messages = list()
        all_scores = []
        all_dst = []

        for etype in range(self.num_edge_types):
            mask = edge_type == etype
            if not mask.any():
                continue

            src, dst = edge_index[:, mask]

            x_src = x[src]
            x_dst = x[dst]

            proj_src = self.proj[etype](x_src).view(-1, self.heads, self.head_dim)
            proj_dst = self.proj[etype](x_dst).view(-1, self.heads, self.head_dim)

            cat = torch.cat([proj_src, proj_dst], dim=-1)  # [E, H, 2D]

            dst_types = node_type[dst]  # [E]
            att = self.att_vec[dst_types]  # [E, 1, H, 2D]

            scores = (cat.unsqueeze(1) * att).sum(dim=-1).squeeze(1)
            scores = F.leaky_relu(scores, 0.2)

            all_messages.append(proj_src)
            all_scores.append(scores)
            all_dst.append(dst)

        msg = torch.cat(all_messages, dim=0)  # [E, H, D]
        scores = torch.cat(all_scores, dim=0)  # [E, H]
        dst = torch.cat(all_dst, dim=0)  # [E]

        alpha = softmax(scores, dst)  # per-dst normalization
        msg = msg * alpha.unsqueeze(-1)

        out = torch.zeros(x.size(0), self.heads, self.head_dim, device=x.device)
        out.index_add_(0, dst, msg)

        return out.view(x.size(0), self.hidden_dim)  # [num_nodes, hidden_dim]
