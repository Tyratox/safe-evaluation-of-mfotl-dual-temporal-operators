(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 *
 * Copyright (C) 2012 ETH Zurich.
 * Contact:  ETH Zurich (Eugen Zalinescu: eugen.zalinescu@inf.ethz.ch)
 *
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, version 2.1 of the
 * License.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see
 * http://www.gnu.org/licenses/lgpl-2.1.html.
 *
 * As a special exception to the GNU Lesser General Public License,
 * you may link, statically or dynamically, a "work that uses the
 * Library" with a publicly distributed version of the Library to
 * produce an executable file containing portions of the Library, and
 * distribute that executable file under terms of your choice, without
 * any of the additional requirements listed in clause 6 of the GNU
 * Lesser General Public License. By "a publicly distributed version
 * of the Library", we mean either the unmodified Library as
 * distributed by Nokia, or a modified version of the Library that is
 * distributed under the conditions defined in clause 3 of the GNU
 * Lesser General Public License. This exception does not however
 * invalidate any other reasons why the executable file might be
 * covered by the GNU Lesser General Public License.
 *)



open Misc
open Predicate
open MFOTL
open Db
open Verified


let elim_double_negation f =
  let rec elim = function
    | Equal (t1, t2) -> Equal (t1, t2)
    | Less (t1, t2) -> Less (t1, t2)
    | LessEq (t1, t2) -> LessEq (t1, t2)
    | Pred p -> Pred p
    | Let (p,f1,f2) -> Let (p,elim f1, elim f2)

    | Neg (Neg f) -> elim f

    | Neg f -> Neg (elim f)
    | And (f1, f2) -> And (elim f1, elim f2)
    | Or (f1, f2) -> Or (elim f1, elim f2)
    | Implies (f1, f2) -> Implies (elim f1, elim f2)
    | Equiv (f1, f2) -> Equiv (elim f1, elim f2)
    | Exists (v, f) -> Exists (v, elim f)
    | ForAll (v, f) -> ForAll (v, elim f)
    | Aggreg (ytyp, y, op, x, glist, f) -> Aggreg (ytyp, y, op, x, glist, elim f)
    | Prev (intv, f) -> Prev (intv, elim f)
    | Next (intv, f) -> Next (intv, elim f)
    | Eventually (intv, f) -> Eventually (intv, elim f)
    | Once (intv, f) -> Once (intv, elim f)
    | Always (intv, f) -> Always (intv, elim f)
    | PastAlways (intv, f) -> PastAlways (intv, elim f)
    | Since (intv, f1, f2) -> Since (intv, elim f1, elim f2)
    | Until (intv, f1, f2) -> Until (intv, elim f1, elim f2)
    | Frex (intv, r) -> Frex (intv, elim_re r)
    | Prex (intv, r) -> Prex (intv, elim_re r)
  and elim_re = function
  | Wild -> Wild
  | Test f -> Test (elim f)
  | Concat (r1,r2) -> Concat(elim_re r1, elim_re r2)
  | Plus (r1,r2) -> Plus(elim_re r1, elim_re r2)
  | Star r -> Star (elim_re r)
  in
  elim f




let simplify_terms f =
  let st t =
    if Predicate.tvars t = []
    then Cst (eval_gterm t)
    else t
  in
  let rec s = function
    | Equal (t1, t2) -> Equal (st t1, st t2)
    | Less (t1, t2) -> Less (st t1, st t2)
    | LessEq (t1, t2) -> LessEq (st t1, st t2)

    | Pred p ->
      let name, _, tlist = Predicate.get_info p in
      let new_tlist = List.map st tlist in
      Pred (Predicate.make_predicate (name, new_tlist))
    | Let (p,f1,f2) -> Let (p, s f1, s f2)
    | Neg f -> Neg (s f)
    | And (f1, f2) -> And (s f1, s f2)
    | Or (f1, f2) -> Or (s f1, s f2)
    | Implies (f1, f2) -> Implies (s f1, s f2)
    | Equiv (f1, f2) -> Equiv (s f1, s f2)
    | Exists (v, f) -> Exists (v, s f)
    | ForAll (v, f) -> ForAll (v, s f)
    | Aggreg (ytyp, y, op, x, glist, f) -> Aggreg (ytyp, y, op, x, glist, s f)
    | Prev (intv, f) -> Prev (intv, s f)
    | Next (intv, f) -> Next (intv, s f)
    | Eventually (intv, f) -> Eventually (intv, s f)
    | Once (intv, f) -> Once (intv, s f)
    | Always (intv, f) -> Always (intv, s f)
    | PastAlways (intv, f) -> PastAlways (intv, s f)
    | Since (intv, f1, f2) -> Since (intv, s f1, s f2)
    | Until (intv, f1, f2) -> Until (intv, s f1, s f2)
    | Frex (intv, r) -> Frex (intv, s_re r)
    | Prex (intv, r) -> Prex (intv, s_re r)
  and s_re = function
  | Wild -> Wild
  | Test f -> Test (s f)
  | Concat (r1,r2) -> Concat(s_re r1, s_re r2)
  | Plus (r1,r2) -> Plus(s_re r1, s_re r2)
  | Star r -> Star (s_re r)
  in
  s f



(* let tt = Equal (Cst (Int 0), Cst (Int 0)) *)


(* This function eliminates the following syntactic sugar: Implies,
   Equiv, ForAll and rewrites the Always and PastAlways operators in
   terms of the Eventually and Once operators *)
let rec elim_syntactic_sugar g =
  let rec elim f =
    match f with
    | Equal _ | Less _ | LessEq _ | Pred _ -> f

    | Let (p,f1,f2) -> Let (p, elim f1, elim f2)
    | Neg f -> Neg (elim f)
    | And (f1, f2) -> And (elim f1, elim f2)
    | Or (f1, f2) -> Or (elim f1, elim f2)
    | Exists (vl, f) ->
      let nf = elim f in
      let new_vl = List.filter
          (fun v -> List.mem v (MFOTL.free_vars nf))
          vl
      in
      if new_vl = [] then nf
      else Exists (new_vl, nf)

    | Implies (f1, f2) -> Or (elim (Neg f1), elim f2)
    | Equiv (f1, f2) -> And
                          (Or (elim (Neg f1), elim f2),
                           Or (elim f1, elim (Neg f2)))
    | ForAll (v, f) -> elim (Neg (Exists (v, Neg f)))

    | Aggreg (ytyp, y, op, x, glist, f) -> Aggreg (ytyp, y, op, x, glist, elim f)


    | Prev (intv, f) -> Prev (intv, elim f)
    | Next (intv, f) -> Next (intv, elim f)
    | Eventually (intv, f) -> Eventually (intv, elim f)
    | Once (intv, f) -> Once (intv, elim f)
    | Always (intv, f) -> Neg (Eventually (intv, elim (Neg f)))
    | PastAlways (intv, f) -> Neg (Once (intv, elim (Neg f)))
    | Since (intv, f1, f2) -> Since (intv, elim f1, elim f2)
    | Until (intv, f1, f2) -> Until (intv, elim f1, elim f2)
    | Frex (intv, r) -> Frex (intv, elim_re r)
    | Prex (intv, r) -> Prex (intv, elim_re r)
  and elim_re = function
  | Wild -> Wild
  | Test f -> Test (elim f)
  | Concat (r1,r2) -> Concat(elim_re r1, elim_re r2)
  | Plus (r1,r2) -> Plus(elim_re r1, elim_re r2)
  | Star r -> Star (elim_re r)
  in
  elim g




(* This function pushes down negation *)
let push_negation g =
  let rec push f = match f with
    | Neg (And (f1, f2)) -> Or ((push (Neg f1)), (push (Neg  f2)))
    | Neg (Or (f1, f2)) -> And ((push (Neg f1)), (push (Neg  f2)))
    | Neg (Eventually (intv, f)) ->
      (* (Always (intv, push (Neg f))) *)
      Neg (Eventually (intv, push f))
    | Neg (Once (intv, f)) ->
      (* (PastAlways (intv, push (Neg f))) *)
      Neg (Once (intv, push f))
    | Neg (Always (intv, f)) ->
      (Eventually (intv, push (Neg f)))
    | Neg (PastAlways (intv, f)) ->
      (Once (intv, push (Neg f)))
    | Neg (Implies (f1, f2) as f) -> push (Neg (push f))
    | Neg (Equiv (f1, f2) as f) -> push (Neg (push f))
    | Neg (Let (p,f1,f2)) -> Let (p,f1, push (Neg f2))

    | Neg f -> Neg (push f)
    | Let (p,f1,f2) -> Let (p,f1, push f2)
    | Equal _ | Less _ | LessEq _ | Pred _ -> f
    | And (f1, f2) -> And (push f1, push f2)
    | Or (f1, f2) -> Or (push f1, push f2)
    | Implies (f1, f2) -> Implies (push f1, push f2)
    | Equiv (f1, f2) -> Equiv (push f1, push f2)
    | Exists (v, f) -> Exists (v, push f)
    | ForAll (v, f) -> ForAll (v, push f)
    | Aggreg (ytyp, y, op, x, glist, f) -> Aggreg (ytyp, y, op, x, glist, push f)
    | Prev (intv, f) -> Prev (intv, push f)
    | Next (intv, f) -> Next (intv, push f)
    | Eventually (intv, f) -> Eventually (intv, push f)
    | Once (intv, f) -> Once (intv, push f)
    | Always (intv, f) -> Always (intv, push f)
    | PastAlways (intv, f) -> PastAlways (intv, push f)
    | Since (intv, f1, f2) -> Since (intv, push f1, push f2)
    | Until (intv, f1, f2) -> Until (intv, push f1, push f2)
    | Frex (intv, r) -> Frex (intv, push_re r)
    | Prex (intv, r) -> Prex (intv, push_re r)
  and push_re = function
  | Wild -> Wild
  | Test f -> Test (push f)
  | Concat (r1,r2) -> Concat(push_re r1, push_re r2)
  | Plus (r1,r2) -> Plus(push_re r1, push_re r2)
  | Star r -> Star (push_re r)
  in
  push g


(* The function [normalize] pushes simplifies terms, eliminates
   syntactic siguar, pushes down negations, and eliminates double
   negations. *)
let normalize f =
  elim_double_negation
    (push_negation
       (elim_syntactic_sugar
          (simplify_terms f)))




(** Detecting monitorable subformulas **)

(* messages explaining the reason for which some subformula is not monitorable *)

let msg_PRED = "In subformulas p(t1,...,tn) each term ti should be a variable or a constant."

let msg_EQUAL = "In input formulas psi of the form t1 = t2 the terms t1 and t2 should be variables or constants and at least one should be a constant."

let msg_LESS = "Formulas of the form t1 < t2 and t1 <= t2 are currently considered not monitorable."

let msg_NOT_EQUAL = "In subformulas psi of the form NOT (t1 = t2) the terms t1 and t2 should be either the same variable x or some constants (except when psi is part of subformulas of the form phi AND NOT psi, or phi AND NOT psi)."

let msg_NOT = "Subformulas of the form NOT psi should contain no free variables (except when they are part of subformulas of the form phi AND NOT psi, NOT psi SINCE_I phi, or NOT psi UNTIL_I phi)."

let msg_ANDRELOP = "In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi."

let msg_SUBSET = "In subformulas of the form phi AND NOT psi, psi SINCE_I phi, and psi UNTIL_I phi, the free variables of psi should be among the free variables of phi."

let msg_OR = "In subformulas of the form phi OR psi, phi and psi should have the same set of free variables."


(* In these special cases, no evaluation is needed for the formula [f2]. *)
let is_special_case fv1 fv2 f2 =
  if Misc.subset fv2 fv1 then
    match f2 with
    | Equal (_, _)
    | Less (_, _)
    | LessEq (_, _)
    | Neg (Equal (_, _))
    | Neg (Less (_, _))
    | Neg (LessEq (_, _))
      -> true
    | _ -> false
  else
    match f2 with
    | Equal (t1, t2) ->
      (match t1, t2 with
       | Var x, t when
           (not (List.mem x fv1))
           && (Misc.subset (Predicate.tvars t) fv1) -> true
       | t, Var x when
           (not (List.mem x fv1))
           && (Misc.subset (Predicate.tvars t) fv1) -> true
       | _ -> false
      )
    | _ -> false


let is_and_relop = function
  | And (_, f) -> (match f with
    | Equal (_, _)
    | Less (_, _)
    | LessEq (_, _)
    | Neg (Equal (_, _))
    | Neg (Less (_, _))
    | Neg (LessEq (_, _)) -> true
    | _ -> false)
  | _ -> failwith "[Rewriting.is_and_relop] internal error"


(* This function tells us beforehand whether a formula is monitorable
   by MonPoly. It should thus exactly correspond to the
   implementation of the Algorithm module.
*)
(* Remark: There are a few formulae that are not TSF safe-range
   (according strictly to the given definition), but which are
   monitorable; and we could accept even a few more: see
   examples/test4.mfotl. However, there are many formulae which are
   TSF safe range but not monitorable since our propagation function
   is still quite limited.
*)
let rec is_monitorable f =
  match f with
  | Equal (t1, t2) ->
    (match t1, t2 with
     | Var _, Cst _
     | Cst _, Var _
     | Cst _, Cst _ -> (true, None)
     | _ -> (false, Some (f, msg_EQUAL))
    )

  | Less _ | LessEq _ ->
    (false, Some (f, msg_LESS))

  | Neg (Equal (t1, t2)) ->
    (match t1, t2 with
     | Var x, Var y when x = y -> (true, None)
     | Cst _, Cst _ -> (true, None)
     | _ -> (false, Some (f, msg_NOT_EQUAL))
    )

  | Pred p ->
    let tlist = Predicate.get_args p in
    if List.for_all (fun t -> match t with Var _ | Cst _ -> true | _ -> false) tlist
    then (true, None)
    else (false, Some (f, msg_PRED))

  | Let (p,f1,f2) ->
    let (is_mon1, r1) = is_monitorable f1 in
    if not is_mon1
    then (is_mon1, r1)
    else is_monitorable f2

  | Neg f1 ->
    if MFOTL.free_vars f1 = [] then
      is_monitorable f1
    else
      (false, Some (f, msg_NOT))

  | And (f1, f2) ->
    let (is_mon1, r1) = is_monitorable f1 in
    if not is_mon1
    then (is_mon1, r1)
    else
      let fv1 = MFOTL.free_vars f1 in
      let fv2 = MFOTL.free_vars f2 in
      if is_and_relop f then
        if is_special_case fv1 fv2 f2
        then (true, None)
        else (false, Some (f, msg_ANDRELOP))
      else
        (match f2 with
         | Neg f2' ->
           if not (Misc.subset fv2 fv1)
           then (false, Some (f, msg_SUBSET))
           else is_monitorable f2'
         | _ -> is_monitorable f2
        )

  | Or (f1, f2) ->
    let fv1 = MFOTL.free_vars f1 in
    let fv2 = MFOTL.free_vars f2 in
    if not (Misc.subset fv1 fv2) || not (Misc.subset fv2 fv1)
    then (false, Some (f, msg_OR))
    else
      let is_mon1, r1 = is_monitorable f1 in
      if not is_mon1
      then (is_mon1, r1)
      else is_monitorable f2

  | Exists (_, f1)
  | Aggreg (_,_,_,_,_,f1)
  | Prev (_, f1)
  | Next (_, f1)
  | Eventually (_, f1)
  | Once (_, f1)
    -> is_monitorable f1

  | Since (intv, f1, f2)
  | Until (intv, f1, f2) ->
    let is_mon2, msg2 = is_monitorable f2 in
    if not is_mon2
    then (is_mon2, msg2)
    else
      let fv1 = MFOTL.free_vars f1 in
      let fv2 = MFOTL.free_vars f2 in
      if not (Misc.subset fv1 fv2)
      then (false, Some (f, msg_SUBSET))
      else
        let f1' = (match f1 with
            | Neg f1' -> f1'
            | _ -> f1)
        in
        is_monitorable f1'
  | Frex (intv , f) -> failwith "[Rewriting.is_monitorable] The future match operator |.|> can be used only with the -verified flag set"
  | Prex (intv , f) -> failwith "[Rewriting.is_monitorable] The past match operator <|.| can be used only with the -verified flag set"

  (* These operators should have been eliminated *)
  | Implies _
  | Equiv _
  | ForAll _
  | Always _
  | PastAlways _ ->
    failwith "[Rewriting.is_monitorable] The operators IMPLIES, EQUIV, FORALL, ALWAYS and PAST_ALWAYS should have been eliminated when the -no_rw option is not present. If the -no_rw option is present, make sure to eliminate these operators yourself."



(** Range-restrictions, safe-range and TSF safe-range checks, and
    propagation of range restrictions
    (see Sec. 5.3.3-5 of Samuel Mueller's PhD thesis) **)





(** returns [(rrv,b)] where [rrv] is the set of ``range restricted''
    variables, with the following difference from the thesis: for a
    subformula [f=Exists (v,f')], [rr f := (rr f') - {v}]. In the
    thesis, the [rr] function is not defined when [v] is not range
    restricted in [f]; when this is the case we set [b] to [false]. So
    when [b=true] then the Samuel's [rr] function is defined (and the
    set of range restricted variables, in our case and in his case,
    coincide. *)
let rec rr = function
  | Pred p -> (Predicate.pvars p, true)

  | Equal (t1, t2) ->
    (match t1, t2 with
     | Var x, Cst c -> ([x], true)
     | Cst c, Var x -> ([x], true)
     | _ -> ([], true) )
  | Less (t1, t2) ->
    (match t1, t2 with
     | Var x, Var y when x=y -> ([x], true)
     | Var x, Cst c -> ([x], true)
     | _ -> ([], true))
  | LessEq (t1, t2) ->
    (match t1, t2 with
     | Var x, Cst c -> ([x], true)
     | _ -> ([], true))

  | Neg (Equal (t1, t2)) ->
    (match t1, t2 with
     | Var x, Var y when x=y -> ([x], true)
     | _ -> ([], true))
  | Neg (Less (t1, t2)) ->
    (match t1, t2 with
     | Cst c, Var x -> ([x], true)
     | _ -> ([], true))
  | Neg (LessEq (t1, t2)) ->
    (match t1, t2 with
     | Var x, Var y when x=y -> ([x], true)
     | Cst c, Var x -> ([x], true)
     | _ -> ([], true))

  | Neg f ->
    let _, b = rr f in
    ([], b)

  | And (f1, Equal (Var x, Var y)) ->
    let (rr1, b) = rr f1 in
    if List.mem x rr1 then
      (Misc.union rr1 [y], b)
    else if List.mem y rr1 then
      (Misc.union rr1 [x], b)
    else
      (rr1, b)

  | And (f1, Less (Var x, Var y)) ->
    let (rr1, b) = rr f1 in
    if List.mem y rr1  || x = y then
      (Misc.union rr1 [x], b)
    else
      (rr1, b)

  | And (f1, Neg (Less (Var x, Var y))) ->
    let (rr1, b) = rr f1 in
    if List.mem x rr1 then
      (Misc.union rr1 [y], b)
    else
      (rr1, b)

  | And (f1, (LessEq (t1, t2)))
  | And (f1, Neg (LessEq (t1, t2))) ->
    let (rr1, b) = rr f1 in
    if b then
      let vars1 = Predicate.tvars t1 in
      let vars2 = Predicate.tvars t2 in
      (rr1, (Misc.subset vars1 rr1) &&
            (Misc.subset vars2 rr1))
    else
      (rr1, b)
  (* failwith "[Rewriting.rr] not yet" *)

  | And (f1, f2) ->
    let (rr1, b1) = rr f1 in
    let (rr2, b2) = rr f2 in
    (Misc.union rr1 rr2, b1 && b2)

  | Or (f1, f2) ->
    let (rr1, b1) = rr f1 in
    let (rr2, b2) = rr f2 in
    (List.filter (fun v -> List.mem v rr1) rr2, b1 && b2)

  | Exists (vl, f) ->
    let (rrf, b) = rr f in
    let rec aux crt_rrf crt_b = function
      | [] -> crt_rrf, crt_b
      | v :: rest ->
        if List.mem v crt_rrf then
          let new_rrf = List.filter (fun x -> x<>v) crt_rrf in
          aux new_rrf crt_b rest
        else
          crt_rrf, false
    in
    aux rrf b vl
  (* if List.mem v rrf then *)
  (*   (List.filter (fun x -> x<>v) rrf, b) *)
  (* else *)
  (*   (rrf, false) *)

  | Aggreg (ytyp, y, op, x, glist, f) ->
    let rrf, b = rr f in
    let frr = List.filter (fun z -> List.mem z glist) rrf in
    y :: frr, b

  | Prev (intv, f) -> rr f
  | Next (intv, f) -> rr f
  | Eventually (intv, f) -> rr f
  | Once (intv, f) -> rr f

  | Since (intv, f1, f2)
  | Until (intv, f1, f2) ->
    let _, b1 = rr f1 in
    let rr2, b2 = rr f2 in
    (rr2, b1 && b2)
  | Frex (_,r) -> rr_re true r 
  | Prex (_,r) -> rr_re false r 
  | Let (_,_,f) -> rr f
  | _ -> failwith "[Rewriting.rr] internal error"
  and rr_re future = function 
  | Wild -> ([],true)
  | Test f -> rr f
  | Concat (r1,r2) -> let (rr1,b1) = rr_re future r1 in
                      let (rr2,b2) = rr_re future r2 in
                      (rr2, b1 && b2)
  | Plus (r1, r2) ->  let (rr1,b1) = rr_re future r1 in
                      let (rr2,b2) = rr_re future r2 in
                      (List.filter (fun v -> List.mem v rr1) rr2, b1 && b2)
  | Star r -> rr_re future r
  



let is_saferange f =
  let rrv, b = rr f in
  b &&
  (
    let rv = List.sort compare rrv in
    let fv = List.sort compare (MFOTL.free_vars f) in
    rv = fv
  )

let is_tsfsaferange f =
  let rec is_tsfsr f =
    let recb =
      Misc.conjunction (
        List.map is_tsfsr (MFOTL.direct_subformulas f))
    in
    if MFOTL.is_temporal f then
      recb && (is_saferange f) &&
      (Misc.conjunction
         (List.map is_saferange (MFOTL.direct_subformulas f)))
    else
      recb
  in
  (is_saferange f) && (is_tsfsr f)


let counter = ref 0

let mk_new_var () =
  let x = "_x" ^ (string_of_int !counter) in
  incr counter;
  x

(* we replace every non-atomic terms by a fresh variable *)
let rewrite_pred p =
  let name, _, term_list = Predicate.get_info p in
  let rec iter replacements nlist tlist =
    match tlist with
    | [] -> replacements, nlist
    | t :: rest ->
      match t with
      | Var _ -> iter replacements (t :: nlist) rest
      | _ ->
        let x = mk_new_var () in
        iter ((t,x) :: replacements) ((Var x) :: nlist) rest
  in
  let replacements, new_tlist = iter [] [] term_list in
  if replacements <> [] then
    let new_pred = Predicate.make_predicate (name, List.rev new_tlist) in
    let eqs = List.fold_left
        (fun f tx -> let t, x = tx in And (f, Equal (Var x, t)))
        (Pred new_pred) (List.rev replacements)
    in
    Exists (List.map snd replacements, eqs)
  else
    Pred p



let propagate_cond f1 f2 =
  let rr1, b1 = rr f1 in
  let rr2, b2 = rr f2 in
  let fv2 = MFOTL.free_vars f2 in
  Misc.inter rr1 (Misc.diff fv2 rr2) <> []


let rec rewrite f =
  match f with
  | And (f', And (f1, f2)) -> (* not a rule of Sec.5.3.4 *)
    if propagate_cond f' f1 then
      rewrite (And (rewrite (And (f', f1)), rewrite f2))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      let f2 = rewrite f2 in
      And (f', And (f1, f2))

  | And (f', Or (f1, f2)) ->
    if propagate_cond f' f1 then
      Or (rewrite (And (f', f1)), rewrite (And (f', f2)))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      let f2 = rewrite f2 in
      And (f', Or (f1, f2))

  | And (f', Exists (v, f1)) ->
    if propagate_cond f' f1 then
      let (v', m) = fresh_var_mapping (free_vars (And (f', f1))) v in
      let m' = List.map (fun (v, n) -> (v, Var n)) m in
      And (f', Exists (replace m v, rewrite (And (f', substitute_vars m' f1))))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      And (f', Exists (v, f1))

  | And (f', Neg (f1)) ->
    if propagate_cond f' f1 && not (is_and_relop f) then
      And (f', Neg (rewrite (And (f', f1))))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      And (f', Neg (rewrite f1))

  | And (f', Prev (intv, f1)) ->
    if propagate_cond f' f1 then
      And (f', Prev (intv, rewrite (And (Next (intv, f'), f1))))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      And (f', Prev (intv, f1))

  | And (f', Next (intv, f1)) ->
    if propagate_cond f' f1 then
      And (f', Next (intv, rewrite (And (Prev (intv, f'), f1))))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      And (f', Next (intv, f1))

  | And (f', Eventually (intv, f1)) ->
    if propagate_cond f' f1 then
      And (f', Eventually (intv, rewrite (And (Once (intv, f'), f1))))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      And (f', Eventually (intv, f1))

  | And (f', Once (intv, f1)) when (snd intv <> Inf) ->
    if propagate_cond f' f1 then
      And (f', Once (intv, rewrite (And (Eventually (intv, f'), f1))))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      And (f', Once (intv, f1))

  | And (f', Since (intv, f1, f2)) when (snd intv <> Inf) ->
    if propagate_cond f' f1 then
      let f1' = rewrite (And (Eventually (init_interval intv, f'), f1)) in
      And (f', Since (intv, f1', f2))
    else if propagate_cond f' f2 then
      let f2' = rewrite (And (Eventually (intv, f'), f2)) in
      And (f', Since (intv, f1, f2'))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      let f2 = rewrite f2 in
      And (f', Since (intv, f1, f2))

  | And (f', Until (intv, f1, f2)) ->
    if propagate_cond f' f1 then
      let f1' = rewrite (And (Once (init_interval intv, f'), f1)) in
      And (f', Until (intv, f1', f2))
    else if propagate_cond f' f2 then
      let f2' = rewrite (And (Once (intv, f'), f2)) in
      And (f', Until (intv, f1, f2'))
    else
      let f' = rewrite f' in
      let f1 = rewrite f1 in
      let f2 = rewrite f2 in
      And (f', Until (intv, f1, f2))

  | Neg f1 -> Neg (rewrite f1)
  | And (f1, f2) -> And (rewrite f1, rewrite f2)
  | Or (f1, f2) -> Or (rewrite f1, rewrite f2)
  | Exists (v, f1) -> Exists (v, rewrite f1)
  | ForAll (v, f1) -> ForAll (v, rewrite f1)
  | Prev (intv, f1) -> Prev (intv, rewrite f1)
  | Next (intv, f1) -> Next (intv, rewrite f1)
  | Eventually (intv, f1) -> Eventually (intv, rewrite f1)
  | Once (intv, f1) -> Once (intv, rewrite f1)
  | Always (intv, f1) -> Always (intv, rewrite f1)
  | PastAlways (intv, f1) -> PastAlways (intv, rewrite f1)
  | Since (intv, f1, f2) -> Since (intv, rewrite f1, rewrite f2)
  | Until (intv, f1, f2) -> Until (intv, rewrite f1, rewrite f2)

  (* | Pred p -> rewrite_pred p *)
  | f -> f


(*** Some syntactic checks *)

let rec check_intervals = 
  let check_interval intv =
    let check_bound b = match b with
    | OBnd a
    | CBnd a -> a >= 0.
    | _ -> true
    in
    let check_lb_ub lb ub =
      match lb, ub with
          | Inf, _ -> false
          | CBnd a, CBnd b -> a<=b
          | CBnd a, OBnd b
          | OBnd a, CBnd b
          | OBnd a, OBnd b -> a < b
          | _ as l , Inf -> l <> Inf
    in
    let lb, ub = intv in
    (check_bound lb) && (check_bound ub) && (check_lb_ub lb ub) in  
function
  | Equal _
  | Less _
  | LessEq _
  | Pred _
    -> true

  | Neg f
  | Exists (_, f)
  | ForAll (_, f)
  | Aggreg (_, _, _, _, _, f)
    -> check_intervals f

  | And (f1, f2)
  | Or (f1, f2)
  | Implies (f1, f2)
  | Equiv (f1, f2)
  | Let (_,f1,f2)
    -> (check_intervals f1) && (check_intervals f2)

  | Eventually (intv, f)
  | Always (intv, f)
  | Prev (intv, f)
  | Next (intv, f)
  | Once (intv, f)
  | PastAlways (intv, f)
    -> (check_interval intv) && (check_intervals f)
    
  | Since (intv, f1, f2)
  | Trigger (intv, f1, f2)
  | Until (intv, f1, f2)
  | Release (intv, f1, f2)
    -> (check_interval intv) && (check_intervals f1) && (check_intervals f2)

  | Frex (intv, r) 
  | Prex (intv, r) 
    -> (check_interval intv) && (check_re_intervals r)
and check_re_intervals = function
  | Wild -> true
  | Test f -> (check_intervals f)
  | Concat (r1,r2)
  | Plus (r1,r2) 
    -> (check_re_intervals r1) && (check_re_intervals r2)
  | Star r -> (check_re_intervals r) 





let rec check_bounds =
  let check_bound intv =
    let _,b = intv in
    match b with
    | Inf -> false
    | _ -> true in
function
  | Equal _
  | Less _
  | LessEq _
  | Pred _
    -> true

  | Neg f
  | Exists (_, f)
  | ForAll (_, f)
  | Aggreg (_, _, _, _, _, f)
  | Prev (_, f)
  | Next (_, f)
  | Once (_, f)
  | PastAlways (_, f)
    -> check_bounds f
  | Prex (intv, r)
    -> check_re_bounds r

  | And (f1, f2)
  | Or (f1, f2)
  | Implies (f1, f2)
  | Equiv (f1, f2)
  | Since (_, f1, f2)
  | Trigger (_, f1, f2)
  | Let (_,f1,f2)
    -> (check_bounds f1) && (check_bounds f2)

  | Eventually (intv, f)
  | Always (intv, f)
    -> (check_bound intv) && (check_bounds f)
  | Frex (intv, r)
    -> (check_bound intv) && (check_re_bounds r)

  | Until (intv, f1, f2)
    -> (check_bound intv) && (check_bounds f1) && (check_bounds f2)
  | Release (intv, f1, f2)
    -> (check_bound intv) && (check_bounds f1) && (check_bounds f2)
and check_re_bounds = function
  | Wild -> true
  | Test f -> (check_bounds f)
  | Concat (r1,r2)
  | Plus (r1,r2) 
    -> (check_re_bounds r1) && (check_re_bounds r2)
  | Star r -> (check_re_bounds r)

  

let rec is_future = function
  | Equal _
  | Less _
  | LessEq _
  | Pred _
    -> false

  | Neg f
  | Exists (_, f)
  | ForAll (_, f)
  | Aggreg (_, _, _, _, _, f)
  | Prev (_, f)
  | Once (_, f)
  | PastAlways (_, f)
    -> is_future f

  | Prex (_,r) -> is_re_future r

  | And (f1, f2)
  | Or (f1, f2)
  | Implies (f1, f2)
  | Equiv (f1, f2)
  | Since (_, f1, f2)
  | Let (_,f1,f2)
    -> (is_future f1) || (is_future f2)

  | Next (_, _)
  | Eventually (_, _)
  | Always (_, _)
  | Until (_, _, _)
  | Frex (_,_)
    -> true
and is_re_future = function 
  | Wild -> false
  | Test f -> (is_future f)
  | Concat (r1,r2)
  | Plus (r1,r2) -> (is_re_future r1) || (is_re_future r2)
  | Star r -> (is_re_future r)

let rec check_let = function
  | Let (p,f1,f2) -> 
    let (n,a,ts) = get_info p in
    let check_params = List.for_all (fun t -> match t with Var _ -> true | _ -> false) ts in
    if not check_params
    then 
      let string_of_terms = List.fold_left (fun s v -> s ^ " " ^ string_of_term v) "" in
      let str = Printf.sprintf "[Rewriting.check_let] LET %s's parameters %s must be variables" n (string_of_terms ts) 
      in failwith str
    else ();
    let prms = List.flatten (List.map tvars ts) in 
    let fv1 = free_vars f1 in
    if (List.length fv1) != a
    then 
      let str = Printf.sprintf "[Rewriting.check_let] LET %s's arity %n must match the number \
      of free variables of %s " n a (string_of_formula "" f1)
      in failwith str
    else ();
    if not (Misc.subset fv1 prms && Misc.subset prms fv1)
    then 
      let string_of_vars = List.fold_left (fun s v -> s ^ " " ^ string_of_var v) "" in
      let str = Printf.sprintf "[Rewriting.check_let] LET %s's parameters %s do not coincide with \
      free variables %s of %s" n (string_of_vars prms) (string_of_vars fv1) (string_of_formula "" f1)
      in failwith str
    else ();
    check_let f2

  | Equal _
  | Less _
  | LessEq _
  | Pred _
    -> true

  | Neg f
  | Exists (_, f)
  | ForAll (_, f)
  | Aggreg (_, _, _, _, _, f)
  | Prev (_, f)
  | Once (_, f)
  | PastAlways (_, f)
  | Next (_, f)
  | Always (_, f)
  | Eventually (_, f)
    -> check_let f

  | Prex (_,r) 
  | Frex (_,r) -> check_re_let r

  | And (f1, f2)
  | Or (f1, f2)
  | Implies (f1, f2)
  | Equiv (f1, f2)
  | Since (_, f1, f2)
  | Trigger (_, f1, f2)
  | Until (_, f1, f2)
  | Release (_, f1, f2)
    -> (check_let f1) && (check_let f2)
and check_re_let = function 
  | Wild -> true
  | Test f -> (check_let f)
  | Concat (r1,r2)
  | Plus (r1,r2) -> (check_re_let r1) && (check_re_let r2)
  | Star r -> (check_re_let r)


type expand_mode = ExpandAll | ExpandNonshared

let expand_let mode f =
  let _ = check_let f in
  let rec expand_let_rec m = function
  | Equal _
  | Less _
  | LessEq _ as f -> f

  | Pred (p)  -> 
    let (n,_,ts) = get_info p in
    if List.mem_assoc n m
    then 
      let (args,f) = List.assoc n m  in
      let args = List.map (fun v -> match v with (Var t) -> t | _ -> failwith "Internal error") args in (* We allow only variables here with check_let *)
      let subm = Misc.zip args ts in
      expand_let_rec (List.remove_assoc n m) (substitute_vars subm f)
    else Pred (p)

  | Let (p, f1, f2) ->
    let name = get_name p in
    (match mode with
    | ExpandAll -> expand_let_rec ((name, (get_args p, f1)) :: m) f2
    | ExpandNonshared ->
      let f2' = expand_let_rec m f2 in
      if count_pred_uses name f2' <= 1 then
        expand_let_rec ((name, (get_args p, f1)) :: m) f2'
      else
        let f1' = expand_let_rec m f1 in
        Let (p, f1', f2'))

  | Neg f -> Neg (expand_let_rec m f)
  | Exists (v, f) -> Exists (v,expand_let_rec m f)
  | ForAll (v, f) -> ForAll (v,expand_let_rec m f)
  | Aggreg (ytyp, y, op, x, g, f) -> Aggreg (ytyp, y,op,x,g, expand_let_rec m f)
  | Prev (i, f) -> Prev (i,expand_let_rec m f)
  | Next (i, f) -> Next (i,expand_let_rec m f)
  | Once (i, f) -> Once (i, expand_let_rec m f)
  | PastAlways (i, f) -> PastAlways (i, expand_let_rec m f)
  | Eventually (i, f) -> Eventually (i, expand_let_rec m f)
  | Always (i, f) -> Always (i, expand_let_rec m f)

  | Prex (i, r) -> Prex (i, expand_let_re_rec m r)
  | Frex (i, r) -> Frex (i, expand_let_re_rec m r)

  | And (f1, f2) -> And (expand_let_rec m f1, expand_let_rec m f2)
  | Or (f1, f2) -> Or (expand_let_rec m f1, expand_let_rec m f2)
  | Implies (f1, f2) -> Implies (expand_let_rec m f1, expand_let_rec m f2)
  | Equiv (f1, f2) ->  Equiv (expand_let_rec m f1, expand_let_rec m f2)
  | Since (i, f1, f2) -> Since (i, expand_let_rec m f1, expand_let_rec m f2)
  | Trigger (i, f1, f2) -> Trigger (i, expand_let_rec m f1, expand_let_rec m f2)
  | Until (i, f1, f2) -> Until (i, expand_let_rec m f1, expand_let_rec m f2)
  | Release (i, f1, f2) -> Release (i, expand_let_rec m f1, expand_let_rec m f2)
and expand_let_re_rec m = function
  | Wild -> Wild 
  | Test f -> Test (expand_let_rec m f)
  | Concat (r1,r2) -> Concat ((expand_let_re_rec m r1), (expand_let_re_rec m r2))
  | Plus (r1,r2) -> Plus (expand_let_re_rec m r1, (expand_let_re_rec m r2))
  | Star r -> Star (expand_let_re_rec m r) in
expand_let_rec [] f


(* We check that
  - any predicate used in the formula is declared in the signature
  - the number of arguments of predicates matches their arity
  - the formula type checks
 [check_syntax db_schema f] returns the list of free variables of [f]
 together with their types
*)

let (<<) f g x = f (g x)

let new_type_symbol cls vs = 
  let maxtype = ((List.fold_left (fun a e -> (max a e)) 0) 
                << (List.map (fun x -> match x with TSymb (_,a) -> a | _ -> -1))
                 << (List.filter (fun x -> match x with TSymb _ -> true | _ -> false)) 
                  << (List.map snd)) vs in
  TSymb (cls, maxtype + 1)

let (|<=|) t1 t2 = match t1, t2 with 
   | TSymb (TNum,a), TSymb (TNum,b) 
   | TSymb (TAny,a), TSymb (TAny,b) -> a <= b
   | TSymb (TNum,_), TSymb (_,_) -> true
   | TSymb _ , _ -> false
   | TCst _ , _ -> true

let type_clash t1 t2 = match t1, t2 with 
   | TCst a, TCst b -> a<>b
   | TSymb (TNum,_), TCst TStr
   | TCst TStr, TSymb (TNum,_) -> true
   | _ -> false

let more_spec_type t1 t2 = if t1 |<=| t2 then t1 else t2 

let string_of_type = function
| TCst TInt -> "Int"
| TCst TFloat -> "Float"
| TCst TStr -> "String"
| TSymb (TNum,a) -> "(Num t" ^ (string_of_int a) ^ ") =>  t" ^ (string_of_int a)
| TSymb (_,a) -> "t" ^ (string_of_int a)

(* 
Checks for type compatibility between t1 and t2

Parameters: 
  t  - term
  t1 - expected type
  t2 - actual type
*)
let type_error t1 t2 t =
  if type_clash t1 t2 then 
        let str = Printf.sprintf "[Rewriting.type_check_term] Type check error on \
        term %s: expected type %s, actual type %s" (string_of_term t) (string_of_type t1) (string_of_type t2)
        in failwith str
  else ()

(* Given that v:t1 and v:t2 for some v,
   check which type is more specific and update ?? accordingly
 *)
 let propagate_constraints t1 t2 vars =
  let update_vars oldt newt  = 
    List.map (fun (v, t) -> if t=oldt then (v,newt) else (v,t)) in
  if (t1 |<=| t2) 
  then update_vars t2 t1 vars 
  else update_vars t1 t2 vars 

(* DEBUG functions *)

let first_debug = ref true

let string_of_delta sch = 
  if (List.length sch > 0)
  then 
    let string_of_types ts = 
      if (List.length ts > 0) 
      then 
        let ft = List.hd ts in 
        List.fold_left (fun a e -> a ^ ", " ^ (string_of_type e)) (string_of_type ft) (List.tl ts)
      else "()" 
    in
    let (fp, fs) = List.hd sch 
    in List.fold_left 
          (fun a (p,ts) -> a ^ ", " ^ p ^ ":(" ^ (string_of_types ts) ^ ")") 
          (fp ^ ":(" ^ (string_of_types fs) ^ ")") (List.tl sch)
  else "_"

let string_of_gamma vars = 
  if (List.length vars > 0)
  then 
  let (fv,ft) = List.hd vars in 
      List.fold_left 
        (fun a (v,t) -> a ^ ", " ^ v ^ ":" ^ (string_of_type t))
      (fv ^ ":" ^ string_of_type ft) (List.tl vars)
  else "_"


(*
Type judgement is of the form (??;??) ??? t::??  
where ?? is the predicate schema
      ?? is the symbol table containing variable types
      t term and 
      ?? is a type

Parameters:
(sch, vars) are (??,??)
typ is the type of t as expected by the caller
t is the term

Returns a triple (??',??', typ') where ??' and ??' are the new ?? and ??
and typ' is the inferred type of t.
Fails of expected (typ) and inferred (typ') types do not match.
*)
let  type_check_term_debug d (sch, vars) typ term = 
  let rec type_check_term (sch, vars) typ term = 
    let _ = 
      if (d) then
      begin
        Printf.printf "[Rewriting.type_check] (%s; %s) ??? " (string_of_delta sch) (string_of_gamma vars);
        Predicate.print_term term;
        Printf.printf ": %s" (string_of_type typ);
        Printf.printf "\n";
      end
      else () in
    match term with 
      | Var v as tt -> 
        if List.mem_assoc v vars then
          let vtyp = (List.assoc v vars) in 
          type_error typ vtyp tt;
          let newvars = propagate_constraints typ vtyp vars in
          (sch, newvars, (List.assoc v vars))  
        else 
          (sch, (v,typ)::vars, typ)
      | Cst c as tt -> 
        let ctyp = TCst (type_of_cst c) in
        type_error typ ctyp tt;
        let newvars = propagate_constraints typ ctyp vars in
        (sch, newvars, ctyp)
      | F2i t as tt ->
        type_error (TCst TInt) typ tt;
        let vars = propagate_constraints typ (TCst TInt) vars in
        let (s,v,t_typ) = type_check_term (sch, vars) (TCst TFloat) t in
        type_error (TCst TFloat) t_typ t;
        let v = propagate_constraints t_typ (TCst TFloat) v in
        (s,v,(TCst TInt))             
      | I2f t as tt ->
        type_error (TCst TFloat) typ tt;
        let vars = propagate_constraints typ (TCst TFloat) vars in
        let (s,v,t_typ) = type_check_term (sch, vars) (TCst TInt) t in
        type_error (TCst TInt) t_typ t;
        let v = propagate_constraints t_typ (TCst TInt) v in
        (s,v,(TCst TFloat))
      | UMinus t as tt -> 
        let exp_typ = new_type_symbol TNum vars in
        type_error exp_typ typ tt;
        let vars = propagate_constraints typ exp_typ vars in
        let (s,v,t_typ) = type_check_term (sch, vars) exp_typ t in
        type_error exp_typ t_typ t;
        let v = propagate_constraints t_typ exp_typ v in
        (s,v,more_spec_type t_typ exp_typ)
      | Plus (t1, t2) 
      | Minus (t1, t2) 
      | Mult (t1, t2)  
      | Div (t1, t2) as tt ->
        let exp_typ = new_type_symbol TNum vars in
        type_error exp_typ typ tt;
        let vars = propagate_constraints typ exp_typ vars in
        let (s1,v1,t1_typ) = type_check_term (sch, vars) exp_typ t1 in
        type_error exp_typ t1_typ t1;
        let v1 = propagate_constraints t1_typ exp_typ v1 in
        let (s2,v2,t2_typ) = type_check_term (s1, v1) t1_typ t2 in
        type_error t1_typ t2_typ t2;
        let v2 = propagate_constraints t2_typ t1_typ v2 in
        (s2,v2,t2_typ)
      | Mod (t1, t2) as tt ->
        let exp_typ = (TCst TInt) in
        type_error exp_typ typ tt;
        let vars = propagate_constraints typ exp_typ vars in
        let (s1,v1,t1_typ) = type_check_term (sch, vars) exp_typ t1 in
        type_error exp_typ t1_typ t1;
        let v1 = propagate_constraints t1_typ exp_typ v1 in
        let (s2,v2,t2_typ) = type_check_term (s1, v1) exp_typ t2 in
        type_error exp_typ t2_typ t2;
        let v2 = propagate_constraints t2_typ exp_typ v2 in
        (s2,v2,exp_typ) in
  type_check_term (sch,vars) typ term


(*
Type judgement is of the form (??;??) ??? ?? wff  
where ?? is the predicate schema
      ?? is the symbol table containing variable types
      ?? formula 

Parameters:
  (sch, vars) are (??,??)
  ?? is an MFOTL formula

Returns a pair (??',??') where ??' and ??' are the new ?? and ??
Fails if ?? is not a well formed formula
*)
let type_check_formula_debug d (sch, vars) = 
let rec type_check_formula (sch, vars) f = 
  let _ = 
    if (d) then
      begin
        Printf.printf "[Rewriting.type_check] (%s; %s) ??? " (string_of_delta sch) (string_of_gamma vars);
        MFOTL.print_formula "" f;
        Printf.printf "\n";
      end
    else () in
  match f with 
  | Equal (t1,t2)
  | Less (t1,t2) 
  | LessEq (t1,t2) as f -> 
    let exp_typ = new_type_symbol TAny vars in
    let (s1,v1,t1_typ) = type_check_term_debug d (sch, vars) exp_typ t1 in
    type_error exp_typ t1_typ t1;
    let v1 = propagate_constraints t1_typ exp_typ v1 in
    let (s2,v2,t2_typ) = type_check_term_debug d (s1, v1) exp_typ t2 in
    type_error exp_typ t2_typ t2;
    let v2 = propagate_constraints t2_typ exp_typ v2 in
    type_error t1_typ t2_typ t2;
    let v2 = propagate_constraints t1_typ t2_typ v2 in
    (s2,v2,f)
  | Pred p as f ->
    let name = Predicate.get_name p in
    let exp_typ_list =
    if List.mem_assoc name sch then
      List.assoc name sch
    else failwith ("[Rewriting.check_syntax] unknown predicate " ^ name  ^
                   " in input formula")
    in 
    let t_list = Predicate.get_args p in 
    if (List.length t_list) = (List.length exp_typ_list) then
      let ts = zip exp_typ_list t_list in  
      let (s,v,_) = 
        List.fold_left 
          (fun (s,v,_) (exp_t,t) -> 
              let (s1,v1,t1) = type_check_term_debug d (s,v) exp_t t in
              type_error exp_t t1 t;
              let v1 = propagate_constraints exp_t t1 v1 in
              (s1,v1,t1)
          ) (sch, vars, (TCst TInt)) ts in
      (s,v,f)
    else 
      failwith ("[Rewriting.check_syntax] wrong arity for predicate " ^ name ^
                " in input formula")
  | Let (p, f1, f2) -> 
    let (n,_,ts) = get_info p in
    let new_vars = List.map (fun v -> match v with (Var t) -> t | _ -> failwith "Internal error") ts in (* We allow only variables here with check_let *)
    let new_typed_vars = List.fold_left (fun vrs vr -> (vr,new_type_symbol TAny vrs)::vrs) [] new_vars in
    let (s1,v1,f1) = type_check_formula (sch, new_typed_vars) f1 in
    assert((List.length v1) = (List.length new_typed_vars));
    let new_sig = List.map (fun v -> (v, List.assoc v v1)) new_vars in
    let new_sig = List.map (fun (_,t) -> t) new_sig in
    let (shadowed_pred,rest) = List.partition (fun (p,_) -> n=p) s1 in
    let delta = (n,new_sig)::rest in
    let (s2, v2, f2) = type_check_formula (delta,vars) f2 in
    let new_delta = List.filter (fun (p,_) -> not (n=p)) s2 in
    (shadowed_pred@new_delta, v2, Let(p,f1,f2))

  | Neg f -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, Neg f)
  | Prev (intv,f) -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, Prev (intv,f))
  | Next (intv,f) -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, Next (intv,f))
  | Eventually (intv,f) -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, Eventually (intv,f))
  | Once (intv,f) -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, Once (intv,f))
  | Always (intv,f)-> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, Always (intv,f))
  | PastAlways (intv,f) -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v, PastAlways (intv,f))

  | And (f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, And(f1, f2))
  | Or (f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Or(f1, f2))
  | Implies (f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Implies(f1, f2))
  | Equiv (f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Equiv(f1, f2))
  | Since (intv,f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Since(intv,f1, f2))
  | Trigger (intv,f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Trigger(intv,f1, f2))
  | Until (intv,f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Until(intv, f1, f2))
  | Release (intv,f1,f2) -> 
    let (s1,v1,f1) = type_check_formula (sch, vars) f1 in
    let (s2,v2,f2) = type_check_formula (s1, v1) f2 in
    (s2, v2, Release(intv,f1, f2))
    

  | Exists (v,f) -> 
    let (shadowed_vars,reduced_vars) = List.partition (fun (vr,_) -> List.mem vr v) vars in
    let new_vars = List.fold_left (fun vrs vr -> (vr,new_type_symbol TAny vrs)::vrs) reduced_vars v in
    let (s1,v1,f) = type_check_formula (sch,new_vars) f in
    let unshadowed_vars = List.filter (fun (vr,_) -> not (List.mem vr v)) v1 in
    (s1,unshadowed_vars@shadowed_vars, Exists (v,f)) 
  | ForAll (v,f) -> 
    let (shadowed_vars,reduced_vars) = List.partition (fun (vr,_) -> List.mem vr v) vars in
    let new_vars = List.fold_left (fun vrs vr -> (vr,new_type_symbol TAny vrs)::vrs) reduced_vars v in
    let (s1,v1,f) = type_check_formula (sch,new_vars) f in
    let unshadowed_vars = List.filter (fun (vr,_) -> not (List.mem vr v)) v1 in
    (s1,unshadowed_vars@shadowed_vars, ForAll (v,f))

  | Aggreg (rty,r,op,x,gs,f) -> 
    let zs = List.filter (fun v -> not (List.mem v gs)) (MFOTL.free_vars f) in
    let (shadowed_vars,reduced_vars) = List.partition (fun (vr,_) -> List.mem vr zs) vars in
    let new_vars = List.fold_left (fun vrs vr -> (vr,new_type_symbol TAny vrs)::vrs) reduced_vars zs in
    let type_check_aggregation exp_typ1 exp_typ2 =
        let (s1,v1,t1) = type_check_term_debug d (sch,new_vars) exp_typ1 (Var r) in
        let shadowed_vars = 
          if (List.mem_assoc r shadowed_vars) 
          then propagate_constraints (List.assoc r shadowed_vars) (List.assoc r v1) shadowed_vars 
          else shadowed_vars
          in
        let (s2,v2,t2) = type_check_term_debug d (s1,v1) exp_typ2 (Var x) in
        let (s3,v3,f) = type_check_formula (s2,v2) f in
        let shadowed_vars = 
          if (exp_typ1 = exp_typ2) && (List.mem_assoc r shadowed_vars)
          then propagate_constraints (List.assoc x v3) (List.assoc r shadowed_vars) shadowed_vars
          else shadowed_vars in 
        let unshadowed_vars = List.filter (fun (vr,_) -> not (List.mem vr zs)) v3 in
        let unshadowed_vars = 
          if (exp_typ1 = exp_typ2) && (List.mem_assoc r unshadowed_vars)
          then propagate_constraints (List.assoc x v3) (List.assoc r unshadowed_vars) unshadowed_vars
          else unshadowed_vars in
        (*TODO add type of r *)
        let v3 = unshadowed_vars@shadowed_vars in
        (s3, v3, Aggreg ((List.assoc r v3), r,op,x,gs,f))
    in
    let exp_typ = new_type_symbol TAny new_vars in
    let exp_num_typ = new_type_symbol TNum new_vars in
    (match op with
      | Min | Max -> type_check_aggregation exp_typ exp_typ
      | Cnt -> type_check_aggregation (TCst TInt) exp_typ
      | Sum -> type_check_aggregation exp_num_typ exp_num_typ
      | Avg | Med -> type_check_aggregation (TCst TFloat) exp_num_typ)
  | Frex (intv,r) -> let (s,v,r) = type_check_re_formula (sch, vars) r in (s,v,Frex (intv,r))
  | Prex (intv,r) -> let (s,v,r) = type_check_re_formula (sch, vars) r in (s,v,Prex (intv,r))
and type_check_re_formula (sch, vars) = function 
  | Wild -> (sch, vars, Wild)
  | Test f -> let (s,v,f) = type_check_formula (sch, vars) f in (s,v,Test f)
  | Concat (r1,r2) ->
    let (s1,v1,r1) = type_check_re_formula (sch, vars) r1 in
    let (s2,v2,r2) = type_check_re_formula (s1, v1) r2 in
    (s2,v2,Concat (r1,r2))
  | Plus (r1,r2) -> 
    let (s1,v1,r1) = type_check_re_formula (sch, vars) r1 in
    let (s2,v2,r2) = type_check_re_formula (s1, v1) r2 in
    (s2,v2,Plus (r1,r2))
  | Star r -> let (s,v,r) = type_check_re_formula (sch, vars) r in (s,v,Star r)
 in
 type_check_formula (sch, vars)



let rec check_syntax db_schema f =
  let lift_type t = TCst t in
  let sch = List.map (fun (t, l) -> (t, List.map (fun (_,t) -> lift_type t) l)) db_schema in 
  let debug = !first_debug && (Misc.debugging Dbg_formula) in 
  let fvs = List.fold_left (fun vrs vr -> (vr,new_type_symbol TAny vrs)::vrs) [] (MFOTL.free_vars f) in
  let (s,v,f) = type_check_formula_debug debug (sch,fvs) f in
  if debug 
    then 
      begin
      Printf.printf "[Rewriting.type_check] The final type judgement is (%s; %s) ??? " (string_of_delta s) (string_of_gamma v);
      MFOTL.print_formula "" f;
      Printf.printf "\n";
      end
    else ();
  first_debug := false;
  (List.map (fun (v,t) -> (v,match t with | TCst a -> a | _ -> TFloat)) v, f)
 


let print_reason str reason =
  match reason with
  | Some (f, msg) ->
    print_string str;
    MFOTL.printnl_formula ", because of the subformula:\n  " f;
    print_endline msg
  | None -> failwith "[Rewriting.print_reason] internal error"

let check_formula check_mon s f =
  (* we first the formula's syntax *)
  let (fv,f) = check_syntax s f in

  (* we then check that it contains wf intervals *)
  if not (check_intervals f) then
    begin
      print_endline "The formula contains a negative or empty interval";
      exit 1;
    end;

  (* we then check that it is a bounded future formula *)
  if not (check_bounds f) then
    begin
      print_endline "The formula contains an unbounded future temporal operator. \
                     It is hence not monitorable.";
      exit 1;
    end;

  if !Misc.no_rw then
    let is_mon, reason = check_mon f in
    if !Misc.verbose || !Misc.checkf then
      begin
        MFOTL.printnl_formula "The input formula is:\n  " f;
        print_string "The sequence of free variables is: ";
        Misc.print_list print_string (MFOTL.free_vars f);
        print_newline();
        if is_mon then print_endline "The formula is monitorable."
        else print_reason "The formula is NOT monitorable" reason
      end
    else if not is_mon then
      print_string "The formula is NOT monitorable. Use the -check or -verbose flags.\n";
    (is_mon, f, fv)
  else
    let nf = normalize f in
    if (Misc.debugging Dbg_monitorable) && nf <> f then
      MFOTL.printnl_formula "The normalized formula is:\n  " nf;

    let is_mon = check_mon nf in
    let rf = if fst is_mon then nf else rewrite nf in
    if (Misc.debugging Dbg_monitorable) && rf <> nf then
      MFOTL.printnl_formula "The \"rewritten\" formula is:\n  " rf;

    (* By default, that is without user specification (see option
       -nonewlastts), we add a new maximal timestamp for future formulas;
       that is, we assume that no more events will happen in the
       future. For past-only formulas we never add such a timestamp. *)
    if not (is_future rf) then
      Misc.new_last_ts := false;

    if !Misc.verbose || !Misc.checkf then
      begin
        if rf <> f then
          MFOTL.printnl_formula "The input formula is:\n  " f;

        MFOTL.printnl_formula "The analyzed formula is:\n  " rf;
        print_string "The sequence of free variables is: ";
        Misc.print_list print_string (MFOTL.free_vars f);
        print_newline()
      end;

    let is_mon = if not (fst is_mon) then check_mon rf else is_mon in
    if (not (fst is_mon)) then
      begin
        if !Misc.verbose || !Misc.checkf then
          begin
            print_reason "The analyzed formula is NOT monitorable" (snd is_mon);
            let is_sr = is_saferange nf in
            (* assert(is_sr = is_saferange rf); *)
            if is_sr then
              print_endline "However, the input (and also the analyzed) formula is safe-range, \n\
                             hence one should be able to rewrite it into a monitorable formula."
            else
              print_endline "The analyzed formula is neither safe-range.";
            let is_tsfsr = is_tsfsaferange rf in
            if is_tsfsr then
              print_endline "By the way, the analyzed formula is TSF safe-range."
            else
              print_endline "By the way, the analyzed formula is not TSF safe-range.";
          end
          else 
            print_string "The formula is NOT monitorable. Use the -check or -verbose flags.\n";
      end
    else if !Misc.checkf then
      print_string "The analyzed formula is monitorable.\n";

    let (fv,rf) = check_syntax s rf in
    (fst is_mon, rf, fv)
