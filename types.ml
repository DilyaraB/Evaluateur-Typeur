#mod_use "evaluateur.ml";;
#load "unix.cma";;
open Unix;;

type ptype = 
  | Var of string 
  | Arr of ptype * ptype  (* fleche *)
  | Nat
  | N
  | List of ptype         (* Type des listes *)
  | Forall of string * ptype  (* Quantification universelle ∀X.T *)
  | Ref of ptype          (* Type des références *)
  | Unit                  (* Type unit *)
  | Weak of ptype

type equa = (ptype * ptype) list 
type env = (string * ptype) list (* une liste d'associations entre vars et types *)
type substitution = (string * ptype) list (* une liste d'associations entre variables de type et leurs types *)

let rec print_type (t : ptype) : string = 
  match t with
  | Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat"
  | N -> "N"
  | List t -> "List(" ^ (print_type t) ^ ")"
  | Forall (x, t) -> "∀" ^ x ^ ". " ^ (print_type t)
  | Ref t -> "Ref(" ^ (print_type t) ^ ")"
  | Unit -> "Unit"
  | Weak t'  -> "Weak (" ^(ptype_to_string t')^ ")"


let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string = 
  compteur_var := !compteur_var + 1;
  "T"^(string_of_int !compteur_var)

(* Rechercher le type d'une variable dans l'environnement *)  
let rec cherche_type (v : string) (e : env) : ptype option =
  match e with 
  | [] -> None  (* On renvoie None si la variable n'est pas trouvée *)
  | (x, ty) :: rest -> if x = v then Some ty else cherche_type v rest


(* Récupère les variables libres dans un type *)
let rec vars_libres (t : ptype) : string list =
  match t with
  | Var x -> [x]
  | Arr (t1, t2) -> (vars_libres t1) @ (vars_libres t2)
  | Nat | N | Unit -> []
  | List t -> vars_libres t
  | Forall (x, t) -> List.filter (fun v -> v <> x) (vars_libres t)
  | Ref t -> vars_libres t
  | Weak t' -> free_vars t'


(* Généraliser un type *)
let generalise_type (t : ptype) (e : env) : ptype =
  let env_vars = List.map fst e in
  let free_vars = vars_libres t in
  let vars_to_generalise = List.filter (fun v -> not (List.mem v env_vars)) free_vars in
  List.fold_right (fun v acc -> Forall (v, acc)) vars_to_generalise t

let generalise_type_weak (t : ptype) (e : env) : ptype =
  let env_vars = List.map fst e in
  let free_vars = vars_libres t in
  let vars_to_generalise = List.filter (fun v -> not (List.mem v env_vars)) free_vars in
  List.fold_right (fun v acc -> Weak (Forall (v, acc))) vars_to_generalise t

let rec is_non_expansive (t : pterm) : bool =
  match t with
  | Var _ -> true
  | Abs (_, _) -> true
  | Int _ -> true
  | Nil -> true
  | Cons (t1, t2) -> is_non_expansive t1 && is_non_expansive t2
  | Add (t1, t2) | Sub (t1, t2) -> is_non_expansive t1 && is_non_expansive t2
  | Let (_, e1, e2) -> is_non_expansive e1 && is_non_expansive e2
  | _ -> false

let rec update_weak_types (env : env) (substitutions : substitution) : env =
  let rec subst_weak t =
    match t with
    | Weak inner ->
        let concrete_type = apply_subst substitutions inner in
        subst_weak concrete_type  (* Continue à substituer jusqu'à ce que le type ne soit plus Weak *)
    | Ref t -> Ref (subst_weak t)
    | List t -> List (subst_weak t)
    | Arr (t1, t2) -> Arr (subst_weak t1, subst_weak t2)
    | Forall (x, t) -> Forall (x, subst_weak t)
    | _ -> apply_subst substitutions t  (* Appliquer les substitutions *)
  in
  List.map (fun (v, t) -> (v, substitute_weak t)) env

let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with
  | Var v -> 
      (match cherche_type v e with
        | Some tv -> [(tv, ty)]  
        | None -> failwith ("Variable " ^ v ^ " non trouvée dans l'environnement"))

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

  | Int _ -> [(ty, N)]

  | Cons (e1, e2) -> 
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa e1 t_elem e in
      let eq2 = genere_equa e2 (List t_elem) e in
      (ty, List t_elem) :: (eq1 @ eq2)

  | Nil -> [(ty, List (Var (nouvelle_var_t ())))]

  | Tete e1 -> 
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa e1 (List t_elem) e in
      (ty, t_elem) :: eq1

  | Queue e1 -> 
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa e1 (List t_elem) e in
      (ty, List t_elem) :: eq1

  | IfZero (e1, e2, e3) -> 
      let eq1 = genere_equa e1 Nat e in
      let eq2 = genere_equa e2 ty e in
      let eq3 = genere_equa e3 ty e in
      eq1 @ eq2 @ eq3

  | IfEmpty (e1, e2, e3) ->
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa e1 (List t_elem) e in
      let eq2 = genere_equa e2 ty e in
      let eq3 = genere_equa e3 ty e in
      eq1 @ eq2 @ eq3

  | Let (x, e1, e2) -> 
      let ta = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa e1 ta e in
      let generalized_ta =
        if is_non_expansive e1 then
          generalise_type ta e
        else
          generalise_type_weak ta e
      in
      let env' = (x, generalized_ta) :: e in
      (* Mise à jour des types faibles avant de générer les équations pour e2 *)
      let updated_env = update_weak_types env' eq1 in
      let eq2 = genere_equa e2 ty updated_env in
      eq1 @ eq2

  | Add (e1, e2) | Sub (e1, e2) ->
      let eq1 = genere_equa e1 N e in
      let eq2 = genere_equa e2 N e in
      (ty, N) :: (eq1 @ eq2)

  | Fix t1 -> 
      let ta = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 (Arr (ta, ta)) e in
      (ty, ta) :: eq1

  | Ref t1 -> 
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 t_elem e in
      (ty, Ref t_elem) :: eq1

  | Deref t1 -> 
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 (Ref t_elem) e in
      (ty, t_elem) :: eq1

  | Assign (t1, t2) -> 
      let t_elem = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 (Ref t_elem) e in
      let eq2 = genere_equa t2 t_elem e in
      (ty, Unit) :: (eq1 @ eq2)

  | Unit -> [(ty, Unit)] 

(* Verifier si une variable appartient a un type *)
let rec occur_check (v : string) (ty : ptype) : bool =
  match ty with 
    | Var x -> x = v
    | Arr (t1, t2) -> (occur_check v t1) || (occur_check v t2)
    | List t | Ref t | Weak t -> occur_check v t
    | Forall (_, t) -> occur_check v t
    | Nat | N | Unit -> false


(* Substitue une variable de type par un autre type dans un type donné *)
let rec subst_type_in_type (v : string) (t_subst : ptype) (t : ptype) : ptype =
  match t with
  | Var x -> if x = v then t_subst else t
  | Arr (t1, t2) -> Arr (subst_type_in_type v t_subst t1, subst_type_in_type v t_subst t2)
  | List t -> List (subst_type_in_type v t_subst t)
  | Ref t -> Ref (subst_type_in_type v t_subst t)
  | Forall (x, t) when x <> v -> Forall (x, subst_type_in_type v t_subst t)
  | Forall (_, _) -> t  (* Si `x` est lié, pas de substitution *)
  | Weak t' -> Weak (subst_type_in_type v t_subst t')
  | Nat | N | Unit -> t    

  
(* Renomme les variables liées pour éviter les conflits *)
let rec barendregtisation (t : ptype) : ptype =
  match t with
  | Forall (x, t) ->
      let new_var = nouvelle_var_t () in
      let t' = subst_type_in_type x (Var new_var) t in
      Forall (new_var, barendregtisation t')
  | Arr (t1, t2) -> Arr (barendregtisation t1, barendregtisation t2)
  | List t -> List (barendregtisation t)
  | Ref t -> Ref (barendregtisation t)
  | Weak t' -> Weak (barendregtisation t')
  | _ -> t

let rec subst_type_in_equa (v : string) (t_subst : ptype) (eqs : equa) : equa =
  List.map (fun (t1, t2) -> 
    (subst_type_in_type v t_subst t1, subst_type_in_type v t_subst t2)) eqs


let rec unify1 (eqs : equa) (s : substitution) : substitution =
  match eqs with 
  | [] -> s 
  | (t1, t2) :: rest when t1 = t2 -> unify1 rest s
  | (Weak t1, t2) :: rest ->
      let t' = barendregtisation t1 in
      unify1 ((t', t2) :: rest) s
  | (t1, Weak t2) :: rest ->
      let t' = barendregtisation t2 in
      unify1 ((t1, t') :: rest) s
  | (Forall (x, t1), t2) :: rest ->
      let t' = barendregtisation t1 in
      unify1 ((t', t2) :: rest) s
  | (t1, Forall (x, t2)) :: rest ->
      let t' = barendregtisation t2 in
      unify1 ((t1, t') :: rest) s
  | (List t1, List t2) :: rest -> unify1 ((t1, t2) :: rest) s
  | (Arr (t1l, t1r), Arr (t2l, t2r)) :: rest ->
      unify1 ((t1l, t2l) :: (t1r, t2r) :: rest) s
  | (Var v, t) :: rest | (t, Var v) :: rest ->
    if occur_check v t then 
      failwith ("Cycle détecté pour la variable " ^ v)
    else 
      let new_s = (v, t) :: s in
      let new_rest = subst_type_in_equa v t rest in
      unify1 new_rest 
  | (Ref t1, Ref t2) :: rest -> unify1 ((t1, t2) :: rest) s
  | (Unit, Unit) :: rest -> unify1 rest s
  | _ -> failwith ("Unification a échoué")


let current_time () = Unix.gettimeofday ()

let rec unify2 (eqs : equa) (s : substitution) (start : float) (timeout : float) : substitution option =
  let time = current_time () -. start in 
  if time >= timeout then None
  else
    match eqs with 
    | [] -> Some s 
    | (t1, t2) :: rest when t1 = t2 -> unify2 rest s start timeout
    | (Weak t1, t2) :: rest ->
        let t' = barendregtisation t1 in
        unify2 ((t', t2) :: rest) s start timeout
    | (t1, Weak t2) :: rest ->
        let t' = barendregtisation t2 in
        unify2 ((t1, t') :: rest) s start timeout
    | (Forall (x, t1), t2) :: rest ->
        let t' = barendregtisation t1 in
        unify2 ((t', t2) :: rest) s start timeout
    | (t1, Forall (x, t2)) :: rest ->
        let t' = barendregtisation t2 in
        unify2 ((t1, t') :: rest) s start timeout
    | (List t1, List t2) :: rest ->
        unify2 ((t1, t2) :: rest) s start timeout
    | (Arr (t1l, t1r), Arr (t2l, t2r)) :: rest ->
        unify2 ((t1l, t2l) :: (t1r, t2r) :: rest) s start timeout
    | (Ref t1, Ref t2) :: rest ->
        unify2 ((t1, t2) :: rest) s start timeout
    | (Var v, t) :: rest | (t, Var v) :: rest ->
        if occur_check v t then 
          None
        else 
          let new_s = (v, t) :: s in
          let new_rest = subst_type_in_equa v t rest in
          unify2 new_rest new_s start timeout
    | (Unit, Unit) :: rest ->
        unify2 rest s start timeout
    | _ -> failwith ("Unification a échoué")


(* Résout un système d'équations avec un timeout *)
let resoudre_avec_timeout (eqs : equa) (timeout : float) : substitution option =
  let start_time = current_time () in
  unify2 eqs [] start_time timeout

(* Applique une substitution à un type donné *)
let rec apply_subst (s : substitution) (t : ptype) : ptype =
  match s with
  | [] -> t
  | (v, t_subst) :: rest ->
    let t' = match t with
      | Weak t_inner -> Weak (apply_subst rest (subst_type_in_type v t_subst t_inner))
      | _ -> subst_type_in_type v t_subst t
    in
    apply_subst rest t'


let infere_type (t : pterm) (timeout : float) : ptype option = 
  let ty = Var (nouvelle_var_t ()) in
  let eqs = genere_equa t ty [] in
  match resoudre_avec_timeout eqs timeout with
  | Some subst -> Some (apply_subst subst ty)
  | None -> None
  