type pterm =
  | Var of string
  | App of pterm * pterm  (*  une application M N *)
  | Abs of string * pterm (*  une abstraction λx.M *)
  | Let of string * pterm * pterm (* let x = e1 in e2 *)
  | Fix of pterm (* fix point*)
  | IfZero of pterm * pterm * pterm (* if zero e1 then e2 else e3 *)
  | IfEmpty of pterm * pterm * pterm (* if empty e1 then e2 else e3 *)
  | Nil 
  | Cons of pterm * pterm (* Cons pour les listes *)
  | Tete of pterm (* Tête d'une liste *)
  | Queue of pterm (* Queue d'une liste *)
  | Int of int (* Entier natif *)
  | Add of pterm * pterm (* Addition d'entiers natifs *)
  | Sub of pterm * pterm (* Soustraction d'entiers natifs *)
  | Ref of pterm                    (* ref e *)
  | Unit 
  | Deref of pterm                  (* !e *)
  | Assign of pterm * pterm         (* e1 := e2 *)

(* Table des états des régions *)
type memory = (int * pterm) list