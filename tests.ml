(* #mod_use "ast.ml";;
#mod_use "evaluateur.ml";;
#mod_use "types.ml";; *)
open Ast;;
open Evaluateur;;
open Types;;
open Printf;;

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

(* Tests pour des termes impliquant Fix et Let *)
let fix_term = Fix (Abs ("f", Abs ("x", IfZero (Var "x", Int 1, App (Var "f", Sub (Var "x", Int 1)))))) (* fix f. λx. if x = 0 then 1 else f (x-1) *)

let let_term = Let ("x", Int 5, Add (Var "x", Int 3)) (* let x = 5 in x + 3 *)

let if_zero_term = IfZero (Int 0, Int 42, Int 0) (* if zero 0 then 42 else 0 *)

let exemples_reduction_complexes = [
  ("Fix Term (factorial-like function)", fix_term);
  ("Let Term (let x = 5 in x + 3)", let_term);
  ("IfZero Term (if zero 0 then 42 else 0)", if_zero_term);
]

(* Tester la réduction *)
let tester_reduction () =
  List.iter (fun (nom, terme) ->
    printf "Test de réduction pour %s :\n" nom;
    match ltr_cbv_norm_timeout terme [] 100 0 with
    | Some (result, _) -> printf "%s\n----\n" (print_term result)
    | None -> print_endline "La réduction a atteint le nombre maximal de pas ou divergence détectée"
  ) exemples_reduction

let tester_reduction_complexe () =
  List.iter (fun (nom, terme) ->
    printf "Test de réduction complexe pour %s :\n" nom;
    match ltr_cbv_norm_timeout terme [] 100 0 with
    | Some (result, _) -> printf "%s\n----\n" (print_term result)
    | None -> print_endline "La réduction a atteint le nombre maximal de pas ou divergence détectée"
  ) exemples_reduction_complexes

(* ------------Tests de substitution ----------- *)
let tester_substitution () =
  let term = App (Var "x", Abs ("y", Var "x")) in
  let substitution_result = substitution "x" (Int 42) term in
  printf "Test de substitution :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après substitution : %s\n" (print_term substitution_result);
  print_endline "----";

  (* Substitution complexe : variable liée dans plusieurs scopes *)
  let term = Abs ("y", App (Var "x", Abs ("y", App (Var "y", Var "x")))) in 
  let substitution_result = substitution "x" (Int 42) term in
  printf "Test de substitution complexe :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après substitution : %s\n" (print_term substitution_result);
  print_endline "----"

let tester_substitution_complexe () =
  (* Substitution avec un Let *)
  let term = Let ("y", Var "x", Add (Var "y", Int 5)) in
  let substitution_result = substitution "x" (Int 10) term in
  printf "Test de substitution complexe (avec Let) :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après substitution : %s\n" (print_term substitution_result);
  print_endline "----";

  (* Substitution avec Fix *)
  let term = Fix (Abs ("f", Add (Var "f", Var "x"))) in
  let substitution_result = substitution "x" (Int 20) term in
  printf "Test de substitution complexe (avec Fix) :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après substitution : %s\n" (print_term substitution_result);
  print_endline "----"

let tester_alphaconv () =
  (* Alphaconversion simple pour éviter les conflits *)
  let term = Abs ("x", Abs ("x", Add (Var "x", Var "y"))) in
  let alphaconv_result = alphaconv term [] in
  printf "Test d'alphaconversion :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après alphaconversion : %s\n" (print_term alphaconv_result);
  print_endline "----";

  (* Alphaconversion pour des termes imbriqués *)
  let term = Abs ("x", App (Abs ("y", App (Var "x", Var "y")), Var "x")) in
  let alphaconv_result = alphaconv term [] in
  printf "Test d'alphaconversion imbriquée :\n";
  printf "Term : %s\n" (print_term term);
  printf "Résultat après alphaconversion : %s\n" (print_term alphaconv_result);
  print_endline "----"
  

(* ------------Tests de typage ----------- *)
(* Tests pour la fonction genere_equa *)
let tester_genere_equa () =
  (* Cas simple : identité *)
  let term = Abs ("x", Var "x") in
  let ty = Var (nouvelle_var_t ()) in
  let env = [] in
  let equations = genere_equa term ty env in
  printf "Test de genere_equa (λx. x) :\n";
  List.iter (fun (t1, t2) ->
    printf "%s = %s\n" (print_type t1) (print_type t2)
  ) equations;
  print_endline "----";

  (* Cas avec une application *)
  let term = App (Abs ("x", Var "x"), Int 5) in
  let ty = Var (nouvelle_var_t ()) in
  let env = [] in
  let equations = genere_equa term ty env in
  printf "Test de genere_equa ((λx. x) 5) :\n";
  List.iter (fun (t1, t2) ->
    printf "%s = %s\n" (print_type t1) (print_type t2)
  ) equations;
  print_endline "----";

  (* Cas plus complexe avec Let *)
  let term = Let ("y", Int 5, Add (Var "y", Int 3)) in
  let ty = Var (nouvelle_var_t ()) in
  let env = [] in
  let equations = genere_equa term ty env in
  printf "Test de genere_equa (let y = 5 in y + 3) :\n";
  List.iter (fun (t1, t2) ->
    printf "%s = %s\n" (print_type t1) (print_type t2)
  ) equations;
  print_endline "----";

  (* Cas avec une quantification universelle *)
  let term = Abs ("x", Var "x") in
  let ty = Forall ("a", Arr (Var "a", Var "a")) in
  let env = [] in
  let equations = genere_equa term ty env in
  printf "Test de genere_equa avec quantification universelle :\n";
  List.iter (fun (t1, t2) ->
    printf "%s = %s\n" (print_type t1) (print_type t2)
  ) equations;
  print_endline "----"

let tester_cherche_type () =
  let env = [("x", Nat); ("y", Arr (Nat, Nat))] in
  printf "Test de cherche_type :\n";
  (match cherche_type "x" env with
  | Some t -> printf "Type de x : %s\n" (print_type t)
  | None -> printf "Type de x : non trouvé\n");
  
  (match cherche_type "y" env with
  | Some t -> printf "Type de y : %s\n" (print_type t)
  | None -> printf "Type de y : non trouvé\n");
  
  (match cherche_type "z" env with
  | Some t -> printf "Type de z : %s\n" (print_type t)
  | None -> printf "Type de z : non trouvé\n");
  
  print_endline "----"

let tester_generalise_type () =
  let t = Arr (Var "a", Var "b") in
  let env = [("a", Nat)] in
  let generalized = generalise_type t env in
  printf "Test de generalise_type :\n";
  printf "Généralisation de %s : %s\n" (print_type t) (print_type generalized);
  print_endline "----";

  (* Cas complexe de généralisation avec plusieurs variables libres *)
  let t = Arr (Var "a", Arr (Var "b", Var "c")) in
  let env = [("a", Nat)] in
  let generalized = generalise_type t env in
  printf "Test de generalise_type complexe :\n";
  printf "Généralisation de %s : %s\n" (print_type t) (print_type generalized);
  print_endline "----"

let tester_subst_type_in_type () =
  let t = Arr (Var "T1", Nat) in
  let t_substitue = subst_type_in_type "T1" Nat t in
  printf "Test de subst_type_in_type :\n";
  printf "Résultat après substitution : %s\n" (print_type t_substitue);
  print_endline "----";

  (* Cas complexe de substitution dans un type imbriqué *)
  let t = Arr (Var "T1", Arr (List (Var "T1"), Var "T2")) in
  let t_substitue = subst_type_in_type "T1" Nat t in
  printf "Test de subst_type_in_type complexe :\n";
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
  match resoudre_avec_timeout eqs 100 with
  | Some subst ->
    List.iter (fun (v, t) ->
      printf "Substitution : %s -> %s\n" v (print_type t)
    ) subst
  | None -> print_endline "Unification échouée ou timeout";
  print_endline "----";

  (* Cas complexe d'unification avec des listes et références *)
  let eqs = [
    (Ref (Var "T1"), Ref (Nat));
    (List (Arr (Var "T2", Nat)), Var "T3");
    (Var "T4", Arr (Var "T2", Ref (Var "T5")))
  ] in
  printf "Test de unify complexe :\n";
  match resoudre_avec_timeout eqs 100 with
  | Some subst ->
    List.iter (fun (v, t) ->
      printf "Substitution : %s -> %s\n" v (print_type t)
    ) subst
  | None -> print_endline "Unification échouée ou timeout";
  print_endline "----"


(* ------------Lancer tous les tests ----------- *)
let () =
  printf "===== Début des tests =====\n";
  tester_reduction ();
  tester_reduction_complexe ();
  tester_substitution ();
  tester_substitution_complexe ();
  tester_alphaconv ();
  tester_genere_equa ();
  tester_cherche_type ();
  tester_generalise_type ();
  tester_subst_type_in_type ();
  tester_unify ();
  printf "===== Fin des tests =====\n";