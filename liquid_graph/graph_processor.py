import torch


class GraphNode:
    def __init__(self, node_id, node_type, name=None):
        self.id = node_id
        self.node_type = node_type
        self.name = name if name else str(node_id)
        self.emb_id = None
        self.data_type = "int"

    def __repr__(self):
        return f"{self.name}"


class LiquidGraph:
    def __init__(self, ast_nodes, variables, constants):
        self.ast_nodes = ast_nodes
        self.variables = variables
        self.constants = constants
        self.node_list = ast_nodes + variables + constants
        self.ast_start = 0
        self.var_start = len(ast_nodes)
        self.const_start = len(ast_nodes) + len(variables)

    def get_var_node(self, idx):
        return self.variables[idx]

    def get_const_node(self, idx):
        return self.constants[idx]


class ProgramContext:
    def __init__(self, ast_nodes, variables, constants):
        # 1. Initialize your existing LiquidGraph
        self.lg = LiquidGraph(ast_nodes, variables, constants)
        self.accumulated_cexs = []

        # 2. EXTRACT VARIABLE NAMES & TYPES
        # We pre-calculate these so updateTree doesn't have to loop every time.
        self.variables = []  # List of strings: ['x', 'y', 'l']
        self.var_types = {}  # Dict: {'x': 'int', 'l': 'list'}

        # Assuming self.lg.variables contains the GraphNode objects you defined earlier
        for var_node in self.lg.variables:
            # Get the name (using str(v) or v.name)
            name = str(var_node)
            self.variables.append(name)

            # Get the type (default to 'int' if missing)
            # This looks for the .data_type attribute you added to GraphNode
            self.var_types[name] = getattr(var_node, "data_type", "int")

    def num_vars(self):
        return len(self.lg.variables)

    def num_consts(self):
        return len(self.lg.constants)

    # (Optional) You can keep this property if other parts of your code use it
    @property
    def variable_names(self):
        return self.variables


class GraphPreprocessor:
    def __init__(self, raw_nodes, raw_edges):
        """
        raw_nodes: List of objects/dicts.
                    [{'id':0, 'type':'stmt'}, {'id':1, 'type':'var'}, ...]
        raw_edges: List of tuples (src_id, dst_id)
        """
        self.raw_nodes = raw_nodes
        self.raw_edges = raw_edges

    def process(self):
        ast_nodes = []
        variables = []
        constants = []

        for node in self.raw_nodes:
            n_type = node.node_type.lower()

            if "var" in n_type:
                variables.append(node)
            elif "const" in n_type or n_type.isdigit():
                constants.append(node)
            else:
                ast_nodes.append(node)

        sorted_nodes = ast_nodes + variables + constants

        # Create an Index Mapping (Old ID -> New Index)
        id_map = {}
        for new_idx, node in enumerate(sorted_nodes):
            old_id = node.id
            id_map[old_id] = new_idx

        new_edges = []
        for src, dst in self.raw_edges:
            if src in id_map and dst in id_map:
                new_src = id_map[src]
                new_dst = id_map[dst]
                new_edges.append((new_src, new_dst))

        return sorted_nodes, new_edges, ast_nodes, variables, constants


# raw_node_list = [
#     GraphNode(name="x", node_type="VAR", original_idx=0),      # ID 0
#     GraphNode(name="+", node_type="OP", original_idx=1),       # ID 1
#     GraphNode(name="1", node_type="CONST", original_idx=2),    # ID 2
#     GraphNode(name="Assign", node_type="STMT", original_idx=3) # ID 3
# ]

# raw_edge_list = [(3, 0), (3, 1)]

# preprocessor = GraphPreprocessor(raw_node_list, raw_edge_list)
# sorted_nodes, new_edges, asts, vars, consts = preprocessor.process()

# program_ctx = ProgramContext(asts, vars, consts)

# print("New Node Order:", sorted_nodes)
# print("New Edges:", new_edges)
