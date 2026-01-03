import torch
import torch.nn as nn

from decoder.pos_encode import TreePosEncode


def weights_init(m):
    """Initializes model weights using Xavier Uniform initialization."""
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
    def __init__(
        self, latent_dim, num_heads=4, num_layers=2, dropout=0.1, ruleset=None
    ):
        super(TransformerDecoder, self).__init__()
        self.d_model = latent_dim
        self.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
        self.vocab_size = 200
        self.fixed_vocab_embed = nn.Embedding(self.vocab_size, latent_dim)
        self.node_proj = nn.Linear(latent_dim, latent_dim)
        self.pos_encoder = TreePosEncode(latent_dim)
        decoder_layer = nn.TransformerDecoderLayer(
            d_model=latent_dim, nhead=num_heads, dropout=dropout
        )
        self.transformer = nn.TransformerDecoder(decoder_layer, num_layers=num_layers)
        self.vocab_head = nn.Linear(latent_dim, self.vocab_size)
        self.pointer_query_proj = nn.Linear(latent_dim, latent_dim)
        self.value_head = nn.Linear(latent_dim, 1)
        self.rule_to_idx = dict()
        self._build_rule_mapping()
        self.current_prompt_idx = None
        weights_init(self)

    def _build_rule_mapping(self):
        idx = 1  # 0 is reserved for START
        idx = 1  # 0 is reserved for START
        common_ops = ["<", ">", "==", "+", "-", "&&", "||", "(", ")"]
        for op in common_ops:
            self.rule_to_idx[op] = idx
            idx += 1

        for key, productions in self.ruleset.items():
            self.rule_to_idx[key] = idx
            idx += 1
            for prod in productions:
                s = str(prod)
                if s not in self.rule_to_idx:
                    self.rule_to_idx[s] = idx
                    idx += 1

    def _process_tree(self, node, env):
        seq_vectors = list()
        depths = list()
        widths = list()
        if node is None:
            # Start Token
            start_token = self.fixed_vocab_embed(torch.tensor([0]).to(self.device))
            seq_vectors.append(start_token)
            depths.append(0)
            widths.append(0)
            if self.current_prompt_idx is not None:
                prompt_vec = self.cached_node_embeddings[
                    self.current_prompt_idx
                ].unsqueeze(0)
                prompt_vec = self.node_proj(prompt_vec)
                seq_vectors.append(prompt_vec)
                depths.append(0)
                widths.append(1)

            return (seq_vectors, depths, widths)
