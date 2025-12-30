import tree_sitter_ocaml
from tree_sitter import Language, Parser


def get_ocaml_tokenizer():
    OCAML_LANG = Language(tree_sitter_ocaml.language_ocaml())
    parser = Parser(OCAML_LANG)

    return parser


def parse(parser, code_str):
    code_bytes = bytes(code_str, "utf8")
    tree = parser.parse(code_bytes)
    tokens = list()
    cursor = tree.walk()

    visited_children = False
    while True:
        if len(cursor.node.children) == 0:
            token_text = code_bytes[
                cursor.node.start_byte : cursor.node.end_byte
            ].decode("utf-8")

            if token_text.strip():
                tokens.append((token_text, cursor.node.type))

        if not visited_children and cursor.goto_first_child():
            visited_children = False
        elif cursor.goto_next_sibling():
            visited_children = False
        elif cursor.goto_parent():
            visited_children = True
        else:
            break

    return tokens

    return tokens


# --- Test ---
if __name__ == "__main__":
    code = """
    let max x y = if x>y then x else y
    """

    try:
        parser = get_ocaml_tokenizer()
        token_list = parse(parser, code)

        print(f"{'TOKEN':<15} {'TYPE'}")
        print("-" * 30)
        for text, type_ in token_list:
            print(f"{text:<15} {type_}")

    except Exception as e:
        print(f"An error occurred: {e}")
