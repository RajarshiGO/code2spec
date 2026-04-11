let rec fac x = match x with
  | 0 | 1 -> 1
  | _ -> x * fac (x-1)
