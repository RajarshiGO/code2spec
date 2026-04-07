type bst = Leaf | Node of int * bst * bst

let rec flat t acc = match t with
  | Leaf -> acc
  | Node(x, l, r) -> flat r (flat l (x :: acc))
