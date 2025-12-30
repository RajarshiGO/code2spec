import torch
import torch.nn as nn
import torch.nn.functional as F
from torch_geometric.nn import MessagePassing
from torch_geometric.utils import softmax


class graphOP(MessagePassing):
    """
    Define message passing and aggregation operator
    """

    def __init__(self, hidden_dim, num_edge_types, heads=1):
        super(graphOP, self).__init__(aggr="add", node_dim=0)
        self.hidden_dim = hidden_dim
        self.num_edge_types = num_edge_types
        self.heads = heads
        self.proj = nn.ModuleList(
            [
                nn.Linear(hidden_dim, hidden_dim * heads, bias=False)
                for _ in range(num_edge_types)
            ]
        )
        # TODO: Splitting the hidden dimension in case of multi-head attention
        self.att_vec = nn.Parameter(torch.Tensor(1, heads, 2 * hidden_dim))
        nn.init.xavier_uniform_(self.att_vec)

    def forward(self, x, edge_index, edge_type):
        """
        x: [num_nodes, hidden_dim]
        edge_index: [2, num_edges]
        edge_type: [num_edges]
        """
        all_messages = list()
        all_indices = list()
        all_attention_scores = list()

        for id in range(self.num_edge_types):
            mask = edge_type == id

            if not mask.any():
                continue

            subset_edge_index = edge_index[:, mask]
            src_indices = subset_edge_index[0]
            dst_indices = subset_edge_index[1]
            x_src = x[src_indices]
            x_dst = x[dst_indices]

            proj_src = self.proj[id](x_src).view(-1, self.heads, self.hidden_dim)
            proj_dst = self.proj[id](x_dst).view(-1, self.heads, self.hidden_dim)
            cat_features = torch.cat([proj_src, proj_dst], dim=-1)
            scores = (cat_features * self.att_vec).sum(dim=-1)
            scores = F.leaky_relu(scores, negative_slope=0.2)
            all_messages.append(proj_src)
            all_attention_scores.append(scores)
            all_indices.append(dst_indices)

        total_msg = torch.cat(all_messages, dim=0)
        total_scores = torch.cat(all_attention_scores, dim=0)
        total_dst = torch.cat(all_indices, dim=0)
        alpha = softmax(total_scores, total_dst)
        out = total_msg * alpha.unsqueeze(-1)
        out_aggregated = torch.zeros(
            x.size(0), self.heads, self.hidden_dim, device=x.device
        )
        out_aggregated.index_add_(0, total_dst, out)

        return out_aggregated.mean(dim=1)
