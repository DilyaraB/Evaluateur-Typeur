#use "evaluateur.ml";;

type ptype = 
  | Var of string 
  | Arr of ptype * ptype  (* fleche *)
  | Nat

type equa = (ptype * ptype) list 
type env = (string * ptype) list (* une liste d'associations entre vars et types *)
type substitution = (string * ptype) list (* une liste d'associations entre variables de type et leurs types *)

let rec print_type (t : ptype) : string = 
  match t with
  | Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^z(print_type t2) ^")"

let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string = compteur_var := !compteur_var + 1;
  "T"^(string_of_int !compteur_var) type equa = (ptype * ptype) list

(* Rechercher le type d'une variable dans l'environnement *)  
let rec cherche_type (v : string) (e : env) : ptype =
  match e with 
    | [] -> failwith ("Variable " ^ v ^ " non trouvée dans l'environement" )
    | (x, ty) :: rest -> if x = v then ty else cherche_type v rest


(* 
1. Si le terme est une variable, elle trouve son type Tv dans l’environnement et g ́en`ere l’ ́equation Tv = T
2. Si le terme est une abstraction, elle prend deux variables de type fraiches Ta et Tr, g ́en`ere l’ ́equation T = Ta → Tr puis g ́en`ere r ́ecursivement les  ́equations du corps de la fonction avec comme cible le type Tr et en rajoutant dans l’environnement que la variable li ́ee par l’abstraction est de type Ta
3. Si le terme est une application, elle prend une variable de type fraˆıche Ta, puis g ́en`ere r ́ecursivement les  ́equations du terme en position de fonction, avec le type cible Ta → T, et les  ́equations du terme en position d’argument avec le type cible Ta, en gardant le mˆeme environnement dans les deux cas
 *)
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

(* Fait une etape d’unification dans les systemes d’equations
1. Si les deux types dans l'equa sont égaux, on supprime l'equa.
2. Si un des deux types est une variable X, qu’elle n’apparait pas dans l’autre type Td, on supprime
l’equa X = Td et on remplace X par Td dans toutes les autres equations.
3. Si les deux types sont des types fleche Tga → Tgr = Tda → Tdr, on supprime l’equa et on ajoute les equations Tga = Tda et Tgr = Tdr
4. Sinon on echoue
*)

let rec unify1 (eqs : equa) (s : substitution) : substitution =
  match eqs with 
  | [] -> s 
  | (t1, t2) :: rest when t1 = t2 -> unify rest s 
  | (Var v, t) :: rest | (t, Var v) :: rest ->
    if occur_check v t then 
      failwith ("Cycle détecté pour la variable " ^ v)
    else 
      let new_s = (v,t) :: s in
      let newRest = subst_type_in_equa v t rest in
      unify newRest new_s
  | (Arr (tga, tgr), Arr (tda, tdr)) :: rest ->
    unify ((t1l, t2l) :: (t1r, t2r) :: rest) s
  |_ -> failwith ("Unification a echoué")


let current_time () = Unix.gettimeofday ()

let rec unify2 (eqs : equa) (s : substitution) (start : float) (timeout : float) : substitution option =
  let time = current_time () -. start in 
  if time >= timeout then None
  else
    match eqs with 
    | [] -> Some s 
    | (t1, t2) :: rest when t1 = t2 -> unify rest s start timeout
    | (Var v, t) :: rest | (t, Var v) :: rest ->
      if occur_check v t then 
        None
      else 
        let new_s = (v,t) :: s in
        let newRest = subst_type_in_equa v t rest in
        unify newRest new_s start timeout
    | (Arr (tga, tgr), Arr (tda, tdr)) :: rest ->
      unify ((t1l, t2l) :: (t1r, t2r) :: rest) s start timeout
    |_ -> None


(* Résout un système d'équations avec un timeout *)
let resoudre_avec_timeout (eqs : equa) (timeout : float) : substitution option =
  let start_time = current_time () in
  unify2 eqs [] start_time timeout

(* Applique une substitution à un type donné *)
let rec apply_subst (s : substitution) (t : ptype) : ptype =
  match s with
  | [] -> t  
  | (v, t_subst) :: rest -> apply_subst rest (subst_type_in_type v t_subst t)  (* substitution (v -> t_subst) au type *)


let infere_type (t : pterm) (timeout : float) : ptype option = 
  let ty = Var (nouvelle_var_t ()) in
  let eqs = genere_equa t ty [] in
  match resoudre_avec_timeout eqs timeout with
  | Some subst -> Some (apply_subst subst ty)
  | None -> None