type pterm =
  | Var of string
  | App of pterm * pterm  (*  une application M N *)
  | Abs of string * pterm (*  une abstraction λx.M *)


(* Conversion des termes en chaines de caracteres lisibles *)
let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t1) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"


let compteur_var = ref 0

let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X" ^ string_of_int !compteur_var

(* Remplace toutes les occurences libres d’une variable donnee par un terme *)
let rec substitution (x : string) (n : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then n else Var y
  | App (t1, t2) -> App (substitution x n t1, substitution x n t2) 
  | Abs (y, t1) -> if y = x then Abs (y, t1) else Abs (y, substitution x n t1)

(* Renomme toutes les variables liees *)
let rec alphaconv1 (t : pterm) : pterm =
  match t with
  | Var x -> Var x (* var libre *)
  | App (t1, t2) -> App (alphaconv1 t1, alphaconv1 t2)
  | Abs (x, t1) -> 
      let newVar = nouvelle_var() in 
      Abs (newVar, alphaconv1 (substitution x (Var newVar) t1))

let rec alphaconv2 (t : pterm) (oldVar : string) : pterm =
  match t with
  | Var x -> if x = oldVar then Var (nouvelle_var ()) else Var x 
  | App (t1, t2) -> App (alphaconv2 t1 oldVar, alphaconv2 t2 oldVar)
  | Abs (x, t1) -> if x = oldVar then Abs(nouvelle_var(), t1) else Abs (x, alphaconv2 t1 oldVar)

(* 
1. Lorsqu'on est face à une application M N, on commence par tenter de réduire M (la fonction), avant de réduire N (l'argument);
2. Variable, abstraction on ne peut pas reduire;
3. La réduction β s'applique uniquement lorsque l'argument est une valeur
 *)

let is_value (t : pterm) : bool =
  match t with 
  | Var _ -> true
  | Abs (_, _) -> true
  | _ -> false

let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with 
  | Var _ -> None
  | Abs(_, _) -> None
  | App ( Abs (x, t1), v2) when is_value v2 ->
    Some (substitution x v2 t1)
  | App (t1, t2) ->
    (match ltr_cbv_step t1 with 
      | Some t1' -> Some (App (t1', t2))(* reduction de la fonction *)
      | None -> match ltr_cbv_step t2 with 
        | Some t2' -> Some (App (t1, t2')) (* reduction de l'argument *)
        | None -> None)

(* Reduit un terme jusqu'a sa forme normale *)
let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_cbv_step t with
  | Some t' -> ltr_cbv_norm t'  (* Si une réduction est possible, continue *)
  | None -> t

  let rec ltr_cbv_norm_timeout (t : pterm) (max_steps : int) (steps : int) : pterm option =
    if steps >= max_steps then
      failwith "Divergence detectee"
    else match ltr_cbv_step t with
      | Some t' -> ltr_cbv_norm_timeout t' max_steps (steps + 1)
      | None -> Some t



