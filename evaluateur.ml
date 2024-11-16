#use "ast.ml";;

(* Conversion des termes en chaines de caracteres lisibles *)
let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t1) -> "(fun " ^ x ^ " -> " ^ (print_term t1) ^ ")"
  | Let (x, t1, t2) -> "let " ^ x ^ " = " ^ (print_term t1) ^ " in " ^ (print_term t2)
  | Fix t1 -> "fix (" ^ (print_term t1) ^ ")"
  | IfZero (e1, e2, e3) -> "if zero " ^ (print_term e1) ^ " then " ^ (print_term e2) ^ " else " ^ (print_term e3)
  | IfEmpty (e1, e2, e3) -> "if empty " ^ (print_term e1) ^ " then " ^ (print_term e2) ^ " else " ^ (print_term e3)
  | Cons (e1, e2) -> "(" ^ (print_term e1) ^ " :: " ^ (print_term e2) ^ ")"
  | Tete e -> "tete (" ^ (print_term e) ^ ")"
  | Queue e -> "queue (" ^ (print_term e) ^ ")"
  | Int n -> string_of_int n
  | Add (e1, e2) -> "(" ^ (print_term e1) ^ " + " ^ (print_term e2) ^ ")"
  | Sub (e1, e2) -> "(" ^ (print_term e1) ^ " - " ^ (print_term e2) ^ ")"
  | Unit -> "()"
  | Ref e -> "ref (" ^ (print_term e) ^ ")"
  | Deref e -> "!(" ^ (print_term e) ^ ")"
  | Assign (e1, e2) -> "(" ^ (print_term e1) ^ " := " ^ (print_term e2) ^ ")"


let compteur_var = ref 0
(* Génère une nouvelle variable *)
let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X" ^ string_of_int !compteur_var


let next_ref_id = ref 0
(* Génère une nouvelle référence *)
let nouvelle_ref () =
  let r = !next_ref_id in
  next_ref_id := !next_ref_id + 1;
  r

(* Fonction auxiliaire pour accéder à une valeur dans la mémoire *)
let rec lookup_ref (ref_id : int) (mem : memory) : pterm option =
  match mem with
  | [] -> None
  | (id, v) :: rest -> if id = ref_id then Some v else lookup_ref ref_id rest

(* Fonction auxiliaire pour mettre à jour la mémoire *)
let rec update_memory (ref_id : int) (value : pterm) (mem : memory) : memory =
  match mem with
  | [] -> [(ref_id, value)]
  | (id, v) :: rest ->
    if id = ref_id then (id, value) :: rest
    else (id, v) :: (update_memory ref_id value rest)

(* Une liste d'associations *)    
type env_subst = (string * string) list

(* Renomme toutes les variables liees *)
let rec alphaconv (t : pterm) (env : env_subst) : pterm =
  match t with
  | Var x ->
      (try Var (List.assoc x env) with Not_found -> Var x)  (* Remplacer si la variable est dans l'environnement *)
  | App (t1, t2) -> App (alphaconv t1 env, alphaconv t2 env)
  | Abs (x, t1) ->
      let new_var = nouvelle_var () in  
      let env' = (x, new_var) :: env in  (* Ajouter la correspondance à l'environnement *)
      Abs (new_var, alphaconv t1 env')
  | Let (x, t1, t2) ->
      let new_var = nouvelle_var () in
      let env' = (x, new_var) :: env in
      Let (new_var, alphaconv t1 env, alphaconv t2 env')
  | Fix t1 -> Fix (alphaconv t1 env)
  | IfZero (e1, e2, e3) -> IfZero (alphaconv e1 env, alphaconv e2 env, alphaconv e3 env)
  | IfEmpty (e1, e2, e3) -> IfEmpty (alphaconv e1 env, alphaconv e2 env, alphaconv e3 env)
  | Cons (e1, e2) -> Cons (alphaconv e1 env, alphaconv e2 env)
  | Tete e -> Tete (alphaconv e env)
  | Queue e -> Queue (alphaconv e env)
  | Int n -> Int n
  | Add (e1, e2) -> Add (alphaconv e1 env, alphaconv e2 env)
  | Sub (e1, e2) -> Sub (alphaconv e1 env, alphaconv e2 env)
  | Ref e -> Ref (alphaconv e env)
  | Deref e -> Deref (alphaconv e env)
  | Assign (e1, e2) -> Assign (alphaconv e1 env, alphaconv e2 env)
  | Unit -> t
  | Nil -> Nil


(* Remplace toutes les occurences libres d’une variable donnee par un terme *)
let rec substitution (x : string) (n : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then n else t
  | App (t1, t2) -> App (substitution x n t1, substitution x n t2)
  | Abs (y, t1) ->
      if y = x then Abs (y, t1)  (* Pas de substitution si la variable est liée *)
      else 
        Abs (y, substitution x n t1)
  | Let (y, t1, t2) ->
      let t1' = substitution x n t1 in
      if y = x then Let (y, t1', t2)  (* Pas de substitution dans le cas d'un `let` *)
      else 
        Let (y, t1', substitution x n t2)
  | Fix t1 -> Fix (substitution x n t1)
  | IfZero (e1, e2, e3) -> IfZero (substitution x n e1, substitution x n e2, substitution x n e3)
  | IfEmpty (e1, e2, e3) -> IfEmpty (substitution x n e1, substitution x n e2, substitution x n e3)
  | Cons (e1, e2) -> Cons (substitution x n e1, substitution x n e2)
  | Tete e -> Tete (substitution x n e)
  | Queue e -> Queue (substitution x n e)
  | Int n' -> Int n'
  | Add (e1, e2) -> Add (substitution x n e1, substitution x n e2)
  | Sub (e1, e2) -> Sub (substitution x n e1, substitution x n e2)
  | Ref e -> Ref (substitution x n e)
  | Deref e -> Deref (substitution x n e)
  | Assign (e1, e2) -> Assign (substitution x n e1, substitution x n e2)
  | Unit -> t
  | Nil -> Nil

let rec is_value (t : pterm) : bool =
  match t with 
  | Var _ -> true
  | Abs (_, _) -> true
  | Int _ -> true
  | Cons (e1, e2) when is_value e1 && is_value e2 -> true
  | _ -> false

(* 
1. Lorsqu'on est face à une application M N, on commence par tenter de réduire M (la fonction), avant de réduire N (l'argument);
2. Variable, abstraction on ne peut pas reduire;
3. La réduction β s'applique uniquement lorsque l'argument est une valeur
 *)
let rec ltr_cbv_step (t : pterm) (mem : memory) : (pterm * memory) option =
  match t with
  | Var _ | Int _ | Abs (_, _) | Nil -> None  (* Ce sont des valeurs, on ne réduit pas *)

  | App (Abs (x, t1), v2) when is_value v2 ->
    Some (substitution x v2 t1, mem)
  | App (t1, t2) ->
    (match ltr_cbv_step t1 mem with 
      | Some (t1', mem') -> Some (App (t1', t2), mem')
      | None -> match ltr_cbv_step t2 mem with 
        | Some (t2', mem') -> Some (App (t1, t2'), mem')
        | None -> None)

  | Let (x, t1, t2) ->
    if is_value t1 then
      Some (substitution x t1 t2, mem)
    else
      (match ltr_cbv_step t1 mem with
      | Some (t1', mem') -> Some (Let (x, t1', t2), mem')
      | None -> None)

  | Fix t1 ->
    (match t1 with
    | Abs (x, t2) -> Some (substitution x (Fix t1) t2, mem)
    | _ -> (match ltr_cbv_step t1 mem with
            | Some (t1', mem') -> Some (Fix t1', mem')
            | None -> None))

  | IfZero (Int 0, t2, _) -> Some (t2, mem)
  | IfZero (Int _, _, t3) -> Some (t3, mem)
  | IfZero (t1, t2, t3) ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (IfZero (t1', t2, t3), mem')
    | None -> None)

  | IfEmpty (Nil, t2, _) -> Some (t2, mem)  (* Si la liste est vide, retourne t2 *)
  | IfEmpty (Cons (_, _), _, t3) -> Some (t3, mem)  (* Si la liste est non vide, retourne t3 *)
  | IfEmpty (t1, t2, t3) ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (IfEmpty (t1', t2, t3), mem')
    | None -> None)

  | Cons (t1, t2) ->
    if is_value t1 && is_value t2 then
      None  (* Une liste construite est une valeur *)
    else if not (is_value t1) then
      (match ltr_cbv_step t1 mem with
      | Some (t1', mem') -> Some (Cons (t1', t2), mem')
      | None -> None)
    else
      (match ltr_cbv_step t2 mem with
      | Some (t2', mem') -> Some (Cons (t1, t2'), mem')
      | None -> None)

  | Tete (Cons (t1, _)) -> Some (t1, mem)  (* Tête d'une liste non vide *)
  | Tete Nil -> failwith "Erreur : Tête d'une liste vide"
  | Tete t1 ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (Tete t1', mem')
    | None -> None)

  | Queue (Cons (_, t2)) -> Some (t2, mem)  (* Queue d'une liste non vide *)
  | Queue Nil -> failwith "Erreur : Queue d'une liste vide"
  | Queue t1 ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (Queue t1', mem')
    | None -> None)

  | Add (Int n1, Int n2) -> Some (Int (n1 + n2), mem)
  | Add (t1, t2) when not (is_value t1) ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (Add (t1', t2), mem')
    | None -> None)
  | Add (v1, t2) when is_value v1 ->
    (match ltr_cbv_step t2 mem with
    | Some (t2', mem') -> Some (Add (v1, t2'), mem')
    | None -> None)

  | Sub (Int n1, Int n2) -> Some (Int (n1 - n2), mem)
  | Sub (t1, t2) when not (is_value t1) ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (Sub (t1', t2), mem')
    | None -> None)
  | Sub (v1, t2) when is_value v1 ->
    (match ltr_cbv_step t2 mem with
    | Some (t2', mem') -> Some (Sub (v1, t2'), mem')
    | None -> None)

  | Ref t1 ->
    if is_value t1 then
      let r = nouvelle_ref () in
      Some (Int r, (r, t1) :: mem)
    else
      (match ltr_cbv_step t1 mem with
      | Some (t1', mem') -> Some (Ref t1', mem')
      | None -> None)

  | Deref (Int r) ->
    (match lookup_ref r mem with
      | Some v -> Some (v, mem)
      | None -> failwith ("Référence non trouvée : " ^ string_of_int r))
  | Deref t1 ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (Deref t1', mem')
    | None -> None)

  | Assign (Int r, v2) when is_value v2 ->
    (match lookup_ref r mem with
      | Some _ ->
        let mem' = update_memory r v2 mem in
        Some (Unit, mem')  (* Retourne une valeur `Unit` symbolique *)
      | None -> failwith ("Référence non trouvée : " ^ string_of_int r))
  | Assign (t1, t2) when not (is_value t1) ->
    (match ltr_cbv_step t1 mem with
    | Some (t1', mem') -> Some (Assign (t1', t2), mem')
    | None -> None)
  | Assign (v1, t2) when is_value v1 ->
    (match ltr_cbv_step t2 mem with
    | Some (t2', mem') -> Some (Assign (v1, t2'), mem')
    | None -> None)

  | _ -> None
  

(* Reduit un terme jusqu'a sa forme normale *)
let rec ltr_cbv_norm (t : pterm) (mem : memory) : (pterm * memory) =
  match ltr_cbv_step t mem with
  | Some (t', mem') -> ltr_cbv_norm t' mem'
  | None -> (t, mem)


let rec ltr_cbv_norm_timeout (t : pterm) (mem : memory) (max_steps : int) (steps : int) : (pterm * memory) option =
  if steps >= max_steps then
    failwith "Divergence detectee"
  else match ltr_cbv_step t mem with
    | Some (t', mem') -> ltr_cbv_norm_timeout t' mem' max_steps (steps + 1)
    | None -> Some (t, mem)
  



