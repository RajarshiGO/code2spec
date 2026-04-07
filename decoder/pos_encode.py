import torch
import torch.nn as nn


class TreePosEncode(nn.Module):
    def __init__(self, d_model: int, max_branch: int = 3):
        super().__init__()
        self.d_model = d_model
        self.max_branch = max_branch
        self.down_matrices = nn.ParameterList(
            [
                nn.Parameter(torch.eye(d_model) + 0.01 * torch.randn(d_model, d_model))
                for _ in range(max_branch)
            ]
        )
        self.base = nn.Parameter(torch.zeros(d_model))

    def encode_path(self, path: list) -> torch.Tensor:
        """
        Args:
            path: list of int child indices from root to this node.
                  []    -> root (BOS)
                  [0]   -> first child of root
                  [1,2] -> third child of second child of root
        Returns:
            Tensor of shape [d_model].
        """
        enc = self.base
        for idx in path:
            idx = min(idx, self.max_branch - 1)
            enc = self.down_matrices[idx] @ enc
        return enc
