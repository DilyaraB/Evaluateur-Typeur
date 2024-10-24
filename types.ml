(* T ::= v | T → T *)


type ptype = 
  | Var of string 
  | Arr of ptype * ptype  (* fleche *)
  | Nat


let rec print_type (t : ptype) : string = 
  match t with
  | Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^z(print_type t2) ^")"

let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string = compteur_var := !compteur_var + 1;
  "T"^(string_of_int !compteur_var) type equa = (ptype * ptype) list

  type equa = (ptype * ptype) list 
  type env = (string * ptype) list (* une liste d'associations entre vars et types *)


(* Rechercher le type d'une variable dans l'environnement *)  
let rec cherche_type (v : string) (e : env) : ptype =
  match e with 
    | [] -> failwith ("Variable " ^ v ^ " non trouvée dans l'environement" )
    | (x, ty) :: rest -> if x = v then ty else cherche_type v rest


let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with
  | Var v -> 
      let tv = cherche_type v e in
      [(tv, ty)]
  | App (t1, t2) -> 
      let ta = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 (Arr (ta, ty)) e in
      let eq2 = genere_equa t2 ta e in 
      eq1 @ eq2
  | Abs (x, t) -> 
      let ta = Var (nouvelle_var_t ()) in
      let tr = Var (nouvelle_var_t ()) in 
      let env' = (x, ta) :: e in
      let equations = genere_equa t tr env' in
      (ty, Arr (ta, tr)) :: equations


(* Verifier si une variable appartient a un type *)

let rec occur_check (v : string) (ty : ptype) : bool =
  match ty with 
    | Var x -> x = v
    | Arr (t1, t2) -> occur_check t1 || occur_check t2
    | Nat -> false


(* Substitue une variable de type par un autre type dans un type donné *)
let rec subst_type_in_type (v : string) (t_subst : ptype) (t : ptype) : ptype =
  match t with
  | Var x -> if x = v then t_subst else t
  | Arr (t1, t2) -> Arr (subst_type_in_type v t_subst t1, subst_type_in_type v t_subst t2)
  | Nat -> Nat      



let rec subst_type_in_equa (v : string) (t_subst : ptype) (eqs : equa) : equa =
  List.map (fun (t1, t2) -> (subst_type_in_type v t_subst t1, subst_type_in_type v t_subst t2)) eqs
