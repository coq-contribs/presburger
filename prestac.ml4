(************************************************************************)
(*                                                                      *)
(*                      prestac.ml                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(* the linking code *)

open Ltac_plugin;;
open Util;;
open CErrors;;
open Term;;
open EConstr;;
open Names;;
open Tacmach;;
open Libnames;;
open Tactics;;
open Termops;;
open Constrintern;;

DECLARE PLUGIN "prestac"

(*i*)

(* First, we need to access some Coq constants
  We do that lazily, because this code can be linked before
  the constants are loaded in the environment
*)

let init_constant c = EConstr.of_constr (Universes.constr_of_global (Coqlib.gen_reference_in_modules "PresTac"
  Coqlib.init_modules c))

let constant c = EConstr.of_constr (Universes.constr_of_global (Coqlib.gen_reference_in_modules "PresTac"
  (Coqlib.init_modules @ Coqlib.zarith_base_modules) c))

let zconstant c = EConstr.of_constr (Universes.constr_of_global (Coqlib.gen_reference_in_modules "PresTac"
  [["Coq";"ZArith";"BinInt"]] c))

(* From logic *)

let coq_ex = lazy (init_constant "ex");;
let coq_eq = lazy (init_constant "eq");;
let coq_and = lazy (init_constant "and");;
let coq_or = lazy (init_constant "or");;
let coq_not = lazy (init_constant "not");;
let coq_True = lazy (init_constant "True");;
let coq_False = lazy (init_constant "False");;
let coq_iff = lazy (init_constant "iff");;
let coq_I = lazy (init_constant "I");;


(* From datatype *)

let coq_prod = lazy (init_constant "prod");;
let coq_s = lazy (init_constant "S");;
let coq_o = lazy (init_constant "O");;


(* From ZArith *)

let coq_z = lazy (constant "Z");;
let coq_xo = lazy (constant "xO");;
let coq_xi = lazy (constant "xI");;
let coq_xh = lazy (constant "xH");;
let coq_zero = lazy (constant "Z0");;
let coq_pos = lazy (constant "Zpos");;
let coq_zplus = lazy (zconstant "add");;


let pres_constant dir s =
  let id = id_of_string s in
  try
    EConstr.of_constr (Universes.constr_of_global (global_reference_in_absolute_module  ( make_dirpath (List.map id_of_string ("Presburger":: dir))) id))
  with _ ->
  try
    EConstr.of_constr (Universes.constr_of_global (global_reference_in_absolute_module  (make_dirpath (List.map id_of_string dir)) id))
  with _ ->     anomaly (Pp.str ("cannot find "^
	     (string_of_qualid (make_qualid  (make_dirpath (List.map id_of_string dir)) id))))

(* From Form *)

let coq_AND = lazy (pres_constant ["Form"; "Presburger"] "ANd");;
let coq_OR = lazy (pres_constant ["Form"; "Presburger"] "Or");;
let coq_IMPL = lazy (pres_constant ["Form"; "Presburger"] "Impl");;
let coq_EQ = lazy (pres_constant ["Form"; "Presburger"] "Eq");;
let coq_NEG = lazy (pres_constant ["Form"; "Presburger"] "Neg");;
let coq_FORALL = lazy (pres_constant ["Form"; "Presburger"] "Forall");;
let coq_EXISTS = lazy (pres_constant ["Form"; "Presburger"] "Exists");;
let coq_PLUS = lazy (pres_constant ["Form"; "Presburger"] "Plus");;
let coq_NUM = lazy (pres_constant ["Form"; "Presburger"] "Num");;
let coq_VAR = lazy (pres_constant ["Form"; "Presburger"] "Var");;

(* From GroundN *)

let coq_fgrounNForm_correct = lazy (pres_constant ["GroundN"; "Presburger"] "fgrounNForm_correct");;

(* From Elim *)

let coq_presburger_correct = lazy (pres_constant ["Elim"; "Presburger"] "presburger_correct");;


(* Some exception *)
exception Not_a_Form


let isDependent sigma t = dependent sigma (mkRel 1) t

(* The conclusion is a propostion, convertConcl returns a pair
      composed of the Expr representing the proposition and
      a hash function containing the interpretation of the variable
*)

let rec pos2Num sigma p =   match (kind sigma p) with
    | App (c,[|t |]) when EConstr.eq_constr sigma c (Lazy.force coq_xo) ->
        2* (pos2Num sigma t)
    | App (c,[|t |]) when EConstr.eq_constr sigma c (Lazy.force coq_xi) ->
        2* (pos2Num sigma t)+1
    | Construct _ when EConstr.eq_constr sigma p (Lazy.force coq_xh) ->
        1
    | a -> raise Not_a_Form

let rec findId c l =  match l with
    | (d::l1) -> if (Id.equal c d) then 0 else (findId c l1)+1
    | a -> raise Not_a_Form

let  isZ sigma p  = match (kind_of_type sigma p) with
    | AtomicType (c,[||]) when EConstr.eq_constr sigma c (Lazy.force coq_z) -> true
    | a -> raise Not_a_Form

let rec convertNum n =
    if n<=0 then Lazy.force coq_o
    else mkApp ((Lazy.force coq_s), [| convertNum (n-1) |])

let rec convertExists sigma l p =   match (kind sigma p) with
(* Lambda *)
    | Lambda (Names.Name c,t1,t2)  when (isZ sigma t1)->
       convert sigma (c::l) t2
    | a -> raise Not_a_Form
and
   convert sigma l p =   match (kind sigma p) with
(* And *)
    | App (c,[|t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_and) ->
        mkApp ((Lazy.force coq_AND), [| convert sigma l t1; convert sigma l t2 |])
(* Or *)
    | App (c,[|t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_or) ->
        mkApp ((Lazy.force coq_OR), [| convert sigma l t1; convert sigma l t2 |])
(* Forall *)
    | Prod (Names.Name c,t1,t2) when EConstr.eq_constr sigma t1 (Lazy.force coq_z) ->
        mkApp ((Lazy.force coq_FORALL), [| convert sigma (c::l) t2 |])
(* Impl *)
    | Prod (c,t1,t2) when Name.equal c Names.Anonymous ->
        mkApp ((Lazy.force coq_IMPL), [| convert sigma l t1; convert sigma l t2 |])
    | Prod (c,t1,t2) when not(dependent sigma (mkRel 1) t2) ->
        mkApp ((Lazy.force coq_IMPL), [| convert sigma l t1; convert sigma l t2 |])
(* Not *)
    | App (c,[|t|]) when EConstr.eq_constr sigma c (Lazy.force coq_not) ->
        mkApp ((Lazy.force coq_NEG), [| convert sigma l t |])
(* Exists *)
    | App (c,[|_; t |]) when EConstr.eq_constr sigma c (Lazy.force coq_ex) ->
        mkApp ((Lazy.force coq_EXISTS), [| convertExists sigma l t |])
(* Eq *)
    | App (c,[|t; t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_eq) ->
        mkApp ((Lazy.force coq_EQ), [| convert sigma l t1; convert sigma l t2 |])
(* Plus *)
    | App (c,[|t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_zplus) ->
        mkApp ((Lazy.force coq_PLUS), [| convert sigma l t1; convert sigma l t2 |])
(* Num *)
    | App (c,[|t |]) when EConstr.eq_constr sigma c (Lazy.force coq_pos) ->
        mkApp ((Lazy.force coq_NUM), [| convertNum (pos2Num sigma t) |])
(* Zero *)
    | Construct _ when EConstr.eq_constr sigma p (Lazy.force coq_zero) ->
        mkApp ((Lazy.force coq_NUM), [| convertNum 0 |])
(* Var *)
    | (Rel  c) ->
        mkApp ((Lazy.force coq_VAR), [| convertNum (c-1) |])

(* Otherwise we generate a new variable if we
   haven't already encounter this term *)
    | a -> raise Not_a_Form



(* Main function *)

let prest_run gl =
  let concl = pf_concl gl in
(* We get the expression and the hastable *)
  let res = convert (project gl) [] concl in
  Proofview.V82.of_tactic
    (exact_check (mkApp ((Lazy.force coq_presburger_correct)
               ,[| res;
                mkApp ((Lazy.force coq_fgrounNForm_correct) ,
                   [| res; Lazy.force coq_o |])
               |]))) gl

TACTIC EXTEND prestac
 [ "prestac" ] -> [ Proofview.V82.tactic prest_run ]
END
