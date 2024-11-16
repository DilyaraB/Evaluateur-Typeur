#mod_use "ast.ml";;
#mod_use "evaluateur.ml";;
#mod_use "types.ml";;

open Printf


(* ------------Combinateurs----------- *)
let i = Abs ("x", Var "x")
let delta = Abs ("x", App (Var "x", Var "x"))  (* δ = λx.(x x) *)
let omega = App (delta, delta) 
let s = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))  (* S = λx.λy.λz.(x z)(y z) *)
let k = Abs ("x", Abs ("y", Var "x"))  (* K = λx.λy.x *)
let skk = App (App (s, k), k)  
let sii = App (App (s, i), i) 


(* ------------Entiers de Church----------- *)

let church_0 = Abs ("f", Abs ("x", Var "x"))  (* λf.λx.x *)
let church_1 = Abs ("f", Abs ("x", App (Var "f", Var "x")))  (* λf.λx.(f x) *)
let church_2 = Abs ("f", Abs ("x", App (Var "f", App (Var "f", Var "x"))))  (* λf.λx.(f (f x)) *)
let church_3 = Abs ("f", Abs ("x", App (Var "f", App (Var "f", App (Var "f", Var "x")))))  (* λf.λx.(f (f (f x))) *)

(* ------------Tests des opérateurs natifs (addition et soustraction)----------- *)
let nat_3 = Int 3
let nat_5 = Int 5
let add_3_5 = Add (nat_3, nat_5) 
let sub_5_3 = Sub (nat_5, nat_3)  
let sub_3_5 = Sub (nat_3, nat_5)  

(* ------------Tests de valeurs ----------- *)
let exemples_reduction = [
  ("I", i);
  ("δ", delta);  
  (* ("Ω", omega);  *)
  ("S", s); 
  ("S K K", skk); 
  ("S I I", sii);  
  ("Church 0", church_0); 
  ("Church 1", church_1);  
  ("Church 2", church_2); 
  ("Church 3", church_3);
  ("Int 3", nat_3);
  ("Int 5", nat_5);
  ("3 + 5", add_3_5);
  ("5 - 3", sub_5_3);
  ("3 - 5", sub_3_5);
]

(* Tester la réduction *)
let tester_reduction () =
  List.iter (fun (nom, terme) ->
    printf "Test de réduction pour %s :\n" nom;
    match ltr_cbv_norm_timeout terme [] 100 0 with
    | Some (result, _) -> printf "%s\n----\n" (print_term result)
    | None -> print_endline "La réduction a atteint le nombre maximal de pas ou divergence détectée"
  ) exemples_reduction

(* ------------Tests de substitution ----------- *)
let tester_substitution () =
  let term = App (Var "x", Abs ("y", Var "x")) in
  let substitution_result = substitution "x" (Int 42) term in
  printf "Test de substitution :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après substitution : %s\n" (print_term substitution_result);
  print_endline "----"

(* ------------Tests de typage ----------- *)
let tester_cherche_type () =
  let env = [("x", Nat); ("y", Arr (Nat, Nat))] in
  printf "Test de cherche_type :\n";
  printf "Type de x : %s\n" (print_type (cherche_type "x" env));
  printf "Type de y : %s\n" (print_type (cherche_type "y" env));
  print_endline "----"

let tester_generalise_type () =
  let t = Arr (Var "a", Var "b") in
  let env = [("a", Nat)] in
  let generalized = generalise_type t env in
  printf "Test de generalise_type :\n";
  printf "Généralisation de %s : %s\n" (print_type t) (print_type generalized);
  print_endline "----"

let tester_subst_type_in_type () =
  let t = Arr (Var "T1", Nat) in
  let t_substitue = subst_type_in_type "T1" Nat t in
  printf "Test de subst_type_in_type :\n";
  printf "Résultat après substitution : %s\n" (print_type t_substitue);
  print_endline "----"

(* Tests pour unify *)
let tester_unify () =
  let eqs = [
    (Arr (Var "T1", Nat), Var "T2");
    (List (Var "T1"), Var "T3");
    (Var "T4", Arr (Var "T1", Var "T5"))
  ] in
  printf "Test de unify :\n";
  match resoudre_avec_timeout eqs 10.0 with
  | Some subst ->
    List.iter (fun (v, t) ->
      printf "Substitution : %s -> %s\n" v (print_type t)
    ) subst
  | None -> print_endline "Unification échouée ou timeout";;
  print_endline "----"


(* ------------Lancer tous les tests ----------- *)
let () =
  printf "===== Début des tests =====\n";
  tester_reduction ();
  tester_substitution ();
  tester_cherche_type ();
  tester_generalise_type ();
  tester_subst_type_in_type ();
  tester_unify ();
  printf "===== Fin des tests =====\n"