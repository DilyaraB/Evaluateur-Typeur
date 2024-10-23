(* T ::= v | T → T *)


type ptype = 
  | Var of string 
  | Arr of ptype * ptype 
  | Nat


let rec print_type (t : ptype) : string = 
  match t with
  | Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^z(print_type t2) ^")"

let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string = compteur_var := !compteur_var + 1;
  "T"^(string_of_int !compteur_var) type equa = (ptype * ptype) list

type env = (string * ptype) list
