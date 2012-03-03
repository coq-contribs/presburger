(************************************************************************)
(*                                                                      *)
(*                      prestac.ml                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(* the linking code *) 

open Pp;;
open Util;;
open Errors;;
open Term;;
open Names;;
open Reduction;;
open Tacmach;;
open Proof_type;;
open Printer;;
open Equality;;
open Vernacinterp;;
open Libnames;;
open Libobject;;
open Closure;;
open Tacred;;
open Tactics;;
open Pattern ;;
open Hiddentac;;
open Termops;;
open Constrintern;;

(*i*)

(* First, we need to access some Coq constants
  We do that lazily, because this code can be linked before
  the constants are loaded in the environment
*)

let init_constant = Coqlib.gen_constant_in_modules "PresTac"
  Coqlib.init_modules

let constant = Coqlib.gen_constant_in_modules "PresTac"
  (Coqlib.init_modules @ Coqlib.zarith_base_modules)

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
let coq_zplus = lazy (constant "Zplus");;


let pres_constant dir s =
  let id = id_of_string s in
  try 
    global_reference_in_absolute_module  ( make_dirpath (List.map id_of_string ("Presburger":: dir))) id
  with _ ->
  try 
    global_reference_in_absolute_module  (make_dirpath (List.map id_of_string dir)) id
  with _ ->     anomaly ("cannot find "^
	     (string_of_qualid (make_qualid  (make_dirpath (List.map id_of_string dir)) id)))

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


let isDependent t = dependent (mkRel 1) t

(* The conclusion is a propostion, convertConcl returns a pair
      composed of the Expr representing the proposition and
      a hash function containing the interpretation of the variable
*)

let rec pos2Num p =   match (kind_of_term p) with
    | App (c,[|t |]) when c=(Lazy.force coq_xo) -> 
        2* (pos2Num t)
    | App (c,[|t |]) when c=(Lazy.force coq_xi) -> 
        2* (pos2Num t)+1
    | Construct _ when p=(Lazy.force coq_xh) ->
        1
    | a -> raise Not_a_Form

let rec findId c l =  match l with
    | (d::l1) -> if (c=d) then 0 else (findId c l1)+1
    | a -> raise Not_a_Form

let  isZ p  = match (kind_of_type p) with
    | AtomicType (c,[||]) when c=(Lazy.force coq_z) -> true
    | a -> raise Not_a_Form

let rec convertNum n = 
    if n<=0 then Lazy.force coq_o
    else mkApp ((Lazy.force coq_s), [| convertNum (n-1) |])

let rec convertExists l p =   match (kind_of_term p) with
(* Lambda *)
    | Lambda (Names.Name c,t1,t2)  when (isZ t1)-> 
       convert (c::l) t2
    | a -> raise Not_a_Form
and
   convert l p =   match (kind_of_term p) with
(* And *)
    | App (c,[|t1; t2|]) when c=(Lazy.force coq_and) -> 
        mkApp ((Lazy.force coq_AND), [| convert l t1; convert l t2 |])
(* Or *)
    | App (c,[|t1; t2|]) when c=(Lazy.force coq_or) -> 
        mkApp ((Lazy.force coq_OR), [| convert l t1; convert l t2 |])
(* Forall *)
    | Prod (Names.Name c,t1,t2) when t1= (Lazy.force coq_z) ->
        mkApp ((Lazy.force coq_FORALL), [| convert (c::l) t2 |])
(* Impl *)
    | Prod (c,t1,t2) when c=Names.Anonymous ->
        mkApp ((Lazy.force coq_IMPL), [| convert l t1; convert l t2 |])
    | Prod (c,t1,t2) when not(dependent (mkRel 1) t2) ->
        mkApp ((Lazy.force coq_IMPL), [| convert l t1; convert l t2 |])
(* Not *)
    | App (c,[|t|]) when c=(Lazy.force coq_not) ->
        mkApp ((Lazy.force coq_NEG), [| convert l t |])
(* Exists *)
    | App (c,[|_; t |]) when c=(Lazy.force coq_ex) -> 
        mkApp ((Lazy.force coq_EXISTS), [| convertExists l t |])
(* Eq *)
    | App (c,[|t; t1; t2|]) when c=(Lazy.force coq_eq) -> 
        mkApp ((Lazy.force coq_EQ), [| convert l t1; convert l t2 |])
(* Plus *)
    | App (c,[|t1; t2|]) when c=(Lazy.force coq_zplus) -> 
        mkApp ((Lazy.force coq_PLUS), [| convert l t1; convert l t2 |])
(* Num *)
    | App (c,[|t |]) when c=(Lazy.force coq_pos) -> 
        mkApp ((Lazy.force coq_NUM), [| convertNum (pos2Num t) |])
(* Zero *)
    | Construct _ when p=(Lazy.force coq_zero) ->
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
  let res = convert [] concl in
       exact_check (mkApp ((Lazy.force coq_presburger_correct)
               ,[| res;
                mkApp ((Lazy.force coq_fgrounNForm_correct) ,
                   [| res; Lazy.force coq_o |])
               |])) gl

TACTIC EXTEND prestac
 [ "prestac" ] -> [ prest_run ]
END
