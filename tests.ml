#use "evaluateur.ml";;


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

let exemples = [
  ("I", i);
  ("δ", delta);  
  ("Ω", omega); 
  ("S", s); 
  ("S K K", skk); 
  ("S I I", sii);  
  ("Church 0", church_0); 
  ("Church 1", church_1);  
  ("Church 2", church_2); 
  ("Church 3", church_3);
]

let tester_exemples () =
  List.iter (fun (nom, terme) ->
    print_endline ("Test de " ^ nom ^ " :");
    let result = ltr_cbv_norm terme in
    print_endline (print_term result);
    print_endline "----"
  ) exemples;;

tester_exemples ();;