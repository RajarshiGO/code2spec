import ast
import json
import re  # Added for regex syntax fixing
import subprocess


class SpecEvaluator:
    def __init__(self, ocaml_binary_path=None):
        """Starts the OCaml binary as a persistent background process."""
        self.process = subprocess.Popen(
            [ocaml_binary_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,  # Line buffered
        )

    def _parse_spec_to_ast(self, spec_string):
        """Converts neural model string to OCaml-compatible JSON AST."""
        tree = ast.parse(spec_string, mode="eval").body

        def visit(node):
            if isinstance(node, ast.Name):
                return {"tag": "Var", "name": node.id}
            elif isinstance(node, ast.Constant):
                if isinstance(node.value, bool):
                    return {"tag": "Lit", "val": {"type": "bool", "val": node.value}}
                elif isinstance(node.value, int):
                    return {"tag": "Lit", "val": {"type": "int", "val": node.value}}
            elif isinstance(node, ast.Compare):
                op_map = {
                    ast.Eq: "eq",
                    ast.NotEq: "neq",
                    ast.Lt: "lt",
                    ast.LtE: "le",
                    ast.Gt: "gt",
                    ast.GtE: "ge",
                }
                left = visit(node.left)
                right = visit(node.comparators[0])
                op_type = type(node.ops[0])
                return {
                    "tag": "BinOp",
                    "op": op_map[op_type],
                    "left": left,
                    "right": right,
                }
            elif isinstance(node, ast.BoolOp):
                op_map = {ast.And: "and", ast.Or: "or"}
                left = visit(node.values[0])
                right = visit(node.values[1])
                return {
                    "tag": "BinOp",
                    "op": op_map[type(node.op)],
                    "left": left,
                    "right": right,
                }
            # --- ADDED THIS TO CATCH OUR DISGUISED '==>' OPERATOR ---
            elif isinstance(node, ast.BinOp):
                if isinstance(node.op, ast.RShift):
                    return {
                        "tag": "BinOp",
                        "op": "==>",
                        "left": visit(node.left),
                        "right": visit(node.right),
                    }
            # --------------------------------------------------------
            elif isinstance(node, ast.Call):
                func_name = node.func.id
                args = [visit(arg) for arg in node.args]
                return {"tag": "App", "name": func_name, "args": args}
            elif isinstance(node, ast.IfExp):
                return {
                    "tag": "ITE",
                    "cond": visit(node.test),
                    "then": visit(node.body),
                    "else": visit(node.orelse),
                }
            raise ValueError(f"Unsupported syntax: {ast.dump(node)}")

        return visit(tree)

    def evaluate(self, spec_string: str, cex: dict) -> bool:
        """Evaluates a specification string against a counterexample."""
        try:
            py = spec_string

            # 1. Manually extract Forall so ast.parse doesn't choke on it
            qvar = None
            if py.startswith("forall"):
                parts = py.split(",", 1)
                qvar = parts[0].replace("forall", "").strip()
                py = parts[1].strip()

            # 2. Disguise OCaml syntax as valid Python syntax
            # a) Convert '==>' into the Python right-shift operator '>>'
            py = py.replace("==>", ">>")

            # b) Convert unparenthesized OCaml functions into Python function calls
            # mem_bst t u -> mem_bst(t, u)
            py = re.sub(
                r"\b(mem_\w+)\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\b", r"\1(\2, \3)", py
            )
            # len_bst t -> len_bst(t)
            py = re.sub(r"\b(len_\w+)\s+([a-zA-Z0-9_]+)\b", r"\1(\2)", py)

            # Standard replacements
            py = (
                py.replace(">=", "GE")
                .replace("<=", "LE")
                .replace("!=", "NEQ")
                .replace("=", "EQ")
            )
            py = py.replace("&&", " and ").replace("||", " or ")
            py = py.replace("true", "True").replace("false", "False")
            py = (
                py.replace("GE", ">=")
                .replace("LE", "<=")
                .replace("NEQ", "!=")
                .replace("EQ", "==")
            )

            # Parse to AST (it is now perfectly valid Python!)
            spec_ast = self._parse_spec_to_ast(py)

            # 3. Wrap the finished AST in the Forall node for OCaml
            if qvar:
                spec_ast = {"tag": "Forall", "qvar": qvar, "body": spec_ast}

            # Send to OCaml Evaluator
            payload = {"spec": spec_ast, "cex": cex}
            self.process.stdin.write(json.dumps(payload) + "\n")
            self.process.stdin.flush()

            # Read response
            response = self.process.stdout.readline().strip()

            if response == "true":
                return True
            if response == "false":
                return False
            if response.startswith("error:"):
                # Print OCaml errors to terminal so they aren't hidden!
                print(f"OCAML ERROR: {response}")
                return False

            return False

        except Exception as e:
            # Print Python parser errors to terminal so they aren't hidden!
            print(f"PYTHON EVALUATOR ERROR: {e}")
            return False

    def close(self):
        """Cleans up the OCaml process."""
        self.process.terminate()


def check_all_cexs(evaluator, code_str, cex_list):
    """Evaluates the code against all counterexamples using the OCaml Evaluator."""
    if not cex_list:
        return True, 0

    passed_count = 0
    for cex in cex_list:
        if evaluator.evaluate(code_str, cex):
            passed_count += 1

    return passed_count == len(cex_list), passed_count
