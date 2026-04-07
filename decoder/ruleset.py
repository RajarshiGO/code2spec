OPREL = ["<", "<=", "=", "!=", ">", ">="]
OPARITH = ["+", "-"]

ADT_SPECS = {
    "list": {
        "measures": ["len_list"],
        "predicates": [("mem_list", 2, "int")],
    },
    "tree": {
        "measures": ["len_tree"],
        "predicates": [("mem_tree", 2, "int")],
    },
    "bst": {
        "measures": ["len_bst"],
        "predicates": [("mem_bst", 2, "int")],
    },
}

QVAR_CANDIDATES = ["u", "w", "z", "y"]


def _fresh_qvar(arg_typed):
    """Pick first candidate not already used as a program argument name."""
    used_names = {name for candidates in arg_typed.values() for _, name in candidates}
    for v in QVAR_CANDIDATES:
        if v not in used_names:
            return v
    raise ValueError(
        f"All quantifier variable candidates {QVAR_CANDIDATES} are taken by program arguments."
    )


def build_ruleset(arg_typed):
    I_prods = []

    # 1. NEW: P_free_prods represents standard propositions ONLY (no qvar)
    P_free_prods = [("I", "oprel", "I")]
    extra = {}
    QI_prods = []

    if arg_typed.get("int") or arg_typed.get("bool"):
        I_prods.append("var_int")
    I_prods.append("const")
    I_prods.append(("I", "oparith", "I"))

    for type_str, candidates in arg_typed.items():
        if type_str in ("int", "bool", "unknown") or not candidates:
            continue
        specs = ADT_SPECS.get(type_str, {"measures": [], "predicates": []})

        for m in specs["measures"]:
            nt = f"{m}_I"
            I_prods.append(nt)
            extra[nt] = [(m, f"var_{type_str}")]

        for pred, arity, elem_type in specs["predicates"]:
            nt = f"{pred}_P"

            if arity == 2:
                has_elem_vars = bool(arg_typed.get(elem_type))

                if has_elem_vars:
                    elem_nt = f"{pred}_elem"
                    extra[elem_nt] = [f"var_{elem_type}", "const"]
                    extra[nt] = [(pred, f"var_{type_str}", elem_nt)]
                    P_free_prods.append(nt)

                qnt = f"{pred}_QI"
                QI_prods.append(qnt)
                extra[qnt] = [(pred, f"var_{type_str}", "qvar")]
            else:
                extra[nt] = [(pred, f"var_{type_str}")]
                P_free_prods.append(nt)

    if QI_prods:
        extra["QI"] = QI_prods
        # Added ("QI", "==>", "QI") back so the grammar natively supports implication
        # between method predicates!
        extra["P"] = ["P_free", "QI", ("QI", "==>", "QI")]

    fresh = _fresh_qvar(arg_typed)
    ruleset = {
        "S": ["P"] if QI_prods else ["P_free"],
        "P_free": P_free_prods,
        "I": I_prods if I_prods else ["const"],
        "oprel": OPREL,
        "oparith": OPARITH,
        "elem_free": ["var_int", "const"],
        "qvar": [fresh],
    }
    ruleset.update(extra)
    return ruleset
