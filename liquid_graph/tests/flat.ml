type bst = Leaf | Node of int * bst * bst

let rec flat t accu = match t with
  | Leaf -> accu
  | Node(x, l, r) -> flat r (flat l (x :: accu))
