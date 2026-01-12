import torch
import torch.nn as nn
import torch.nn.functional as F

from decoder.pos_encode import TreePosEncode


class Node:
    def __init__(self, rule=None, name=None, lg_node=None):
        self.rule = rule
        self.name = name  # Terminal token
        self.lg_node = lg_node  # Reference to Graph Node
        self.children = list()
        self.parent = None

    def add_child(self, node):
        node.parent = self
        self.children.append(node)

    def __repr__(self):
        if self.name:
            return self.name
        if self.rule:
            return str(self.rule)
        return "Node"


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
        self.ruleset = ruleset if ruleset else DEFAULT_RULESET  # will add later
        self.device = "cuda" if torch.cuda.is_available() else "cpu"
        self.max_depth = 10
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
        self.latent_state = None
        self.nll = 0.0
        self.apply(weights_init)
        weights_init(self)

    def _build_rule_mapping(self):
        idx = 1  # 0 is reserved for START
        common_ops = ["<", ">", "==", "+", "-", "&&", "||"]
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

    def _get_node_embedding(self, n, program_ctx):
        """
        Helper to convert a single node into an embedding vector.
        """
        if n.lg_node is not None:
            try:
                node_idx = program_ctx.lg.node_list.index(n.lg_node)
                vec = self.cached_node_embeddings[node_idx].unsqueeze(0)
                return self.node_proj(vec)
            except ValueError:
                pass

        idx = 0
        if n.rule and str(n.rule) in self.rule_to_idx:
            idx = self.rule_to_idx[str(n.rule)]
        elif n.name and n.name in self.rule_to_idx:
            idx = self.rule_to_idx[n.name]
        else:
            val = n.name if n.name else str(n.rule)
            idx = abs(hash(val)) % self.vocab_size

        return self.fixed_vocab_embed(torch.tensor([idx]).to(self.device))

    def _traverse_tree(
        self, node, program_ctx, seq_vectors, depths, widths, curr_depth, curr_width
    ):
        """
        Helper for recursive traversal.
        """
        if node is None:
            return

        vec = self._get_node_embedding(node, program_ctx)
        seq_vectors.append(vec)
        depths.append(curr_depth)
        widths.append(curr_width)

        for i, child in enumerate(node.children):
            self._traverse_tree(
                child, program_ctx, seq_vectors, depths, widths, curr_depth + 1, i
            )

    def _process_tree(self, node, program_ctx):
        seq_vectors = list()
        depths = list()
        widths = list()
        if self.current_prompt_idx is not None:
            prompt_vec = self.node_proj(
                self.cached_node_embeddings[self.current_prompt_idx].unsqueeze(0)
            )
            seq_vectors.append(prompt_vec)
            depths.append(0)
            widths.append(1)

        start_token = self.fixed_vocab_embed(torch.tensor([0]).to(self.device))
        seq_vectors.insert(0, start_token)
        depths.insert(0, 0)
        widths.insert(0, 0)

        if node is not None:
            self._traverse_tree(node, program_ctx, seq_vectors, depths, widths, 0, 0)

        return seq_vectors, depths, widths

    def transformer_step(self, history):
        vectors, depths, widths = history

        x = torch.cat(vectors, dim=0).unsqueeze(1)
        d_idx = torch.tensor(depths).to(self.device).unsqueeze(1)
        w_idx = torch.tensor(widths).to(self.device).unsqueeze(1)

        x = x + self.tree_pos_encoder(d_idx, w_idx)

        sz = x.size(0)
        tgt_mask = self.transformer.generate_square_subsequent_mask(sz).to(self.device)
        memory = self.cached_node_embeddings.unsqueeze(1)

        output = self.transformer(x, memory, tgt_mask=tgt_mask)
        return output[-1, 0, :]

    def choose_action(self, state, cls_w, use_random, eps):
        # Dense Embeddings = Pointer Task, Sparse/Identity = Grammar Task
        is_pointer_task = True
        if cls_w.dim() == 2 and cls_w.shape[0] == cls_w.shape[1]:
            if torch.all(cls_w.eq(0) | cls_w.eq(1)):
                is_pointer_task = False

        if is_pointer_task:
            query = self.pointer_query_proj(state).unsqueeze(0)
            logits = torch.mm(query, cls_w.t())
        else:
            full_logits = self.vocab_head(state)
            logits = full_logits[0 : cls_w.shape[0]].unsqueeze(0)

        ll = F.log_softmax(logits, dim=1)

        if use_random:
            # Introduce some noise preferably during training
            scores = torch.exp(ll) * (1 - eps) + eps / ll.shape[1]
            picked = torch.multinomial(scores, 1)
        else:
            # Greedy Decoding preferably during inference
            _, picked = torch.max(ll, 1)

        picked = picked.view(-1)
        self.nll += F.nll_loss(ll, picked)
        return picked

    def updateTree(self, program_ctx, node, use_random, eps, depth=0):
        if depth > self.max_depth:
            return node
        if node.name is not None or node.children:
            return node

        symbol = node.rule
        if symbol not in self.ruleset:
            return node

        productions = self.ruleset.get(symbol, [])

        history = self._process_tree(self.root, program_ctx)
        self.latent_state = self.transformer_step(history)

        if len(productions) > 0:
            cls_w = torch.eye(len(productions)).to(self.device)
        elif symbol == "var":
            num_vars = program_ctx.num_vars()
            cls_w = self.cached_node_embeddings[0:num_vars, :]
        elif symbol == "const":
            num_vars = program_ctx.num_vars()
            num_consts = program_ctx.num_consts()
            cls_w = self.cached_node_embeddings[num_vars : num_vars + num_consts, :]
        else:
            return node

        choice_idx = self.choose_action(self.latent_state, cls_w, use_random, eps)

        if symbol == "var" or symbol == "const":
            offset = 0 if symbol == "var" else program_ctx.num_vars()
            lg_node = program_ctx.lg.node_list[offset + choice_idx]
            node.name = str(lg_node)
            node.lg_node = lg_node
        else:
            selected_prod = productions[choice_idx]
            for token in selected_prod:
                child = Node(rule=token, name=None if token in self.ruleset else token)
                node.add_child(child)

            for child in node.children:
                self.updateTree(program_ctx, child, use_random, eps, depth + 1)

        return node

    def forward(
        self, program_ctx, node_embedding, use_random, eps=0.05, target_var_idx=None
    ):
        self.cached_node_embeddings = node_embedding
        self.program_ctx = program_ctx
        self.nll = 0
        self.current_prompt_idx = target_var_idx
        initial_history = self._process_tree(None, program_ctx)
        initial_state = self.transformer_step(initial_history)
        est = self.value_head(initial_state)
        self.root = Node(rule="S", name=None)
        self.root = self.updateTree(program_ctx, self.root, use_random, eps)

        return self.root, self.nll, est
