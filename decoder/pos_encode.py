import torch.nn as nn



class TreePosEncode(nn.Module):
    def __init__(self, d_model, max_depth=50, max_width=20):
        super(TreePosEncode, self).__init__()
        self.depth_embed = nn.Embedding(max_depth, d_model)
        self.width_embed = nn.Embedding(max_width, d_model)
        nn.init.uniform_(self.depth_embed.weight, -0.05, 0.05)
        nn.init.uniform_(self.width_embed.weight, -0.05, 0.05)

    def forward(self, depth_indices, width_indices):
        """
        Args:
            depth_indices: Tensor [Seq_Len, 1]
            width_indices: Tensor [Seq_Len, 1]
        """
        d_idx = depth_indices.clamp(0, self.depth_embed.num_embeddings - 1)
        w_idx = width_indices.clamp(0, self.width_embed.num_embeddings - 1)
        d = self.depth_embed(d_idx)
        w = self.width_embed(w_idx)

        return d + w
