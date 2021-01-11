(* StardustML compiler
   Copyright 2001-2013 Joshua Dunfield
    
   This program is free software: you can redistribute it and/or modify it under
   the terms of the GNU General Public License as published by the Free Software
   Foundation, either version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but WITHOUT ANY
   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
   FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

   You should have received a copy of the GNU General Public License along with this
   program, in a file called COPYING. If not, see <http://www.gnu.org/licenses/>.
*)
(* File: Subst.sml
   Author: Joshua Dunfield
   Contents: Substitution for program variables in expressions

   History: 2012-01-30 [jcd] -- Created.
*)

signature SUBST = sig

  val rename : {from : Sdml.pv, to : Sdml.pv} -> Sdml.exp -> Sdml.exp
  val subst : (Sdml.pv * Sdml.exp) -> Sdml.exp -> Sdml.exp

  val rename_locexp : {from : Sdml.pv, to : Sdml.pv} -> Sdml.locexp -> Sdml.locexp
  val subst_locexp : (Sdml.pv * Sdml.exp) -> Sdml.locexp -> Sdml.locexp

  val rename_locexp_mass : (Sdml.pv * Sdml.pv) list -> Sdml.locexp -> Sdml.locexp

end

structure Subst :> SUBST = struct

  open Sdml

  structure P = Print
  

  fun subst (pv, replacement) exp =
      let val f = subst_locexp (pv, replacement)
      in
        case exp of
            Const(texp, string) => Const(texp, string)
          | Var pv' => if pv = pv' then replacement else Var pv'
          | Con con => Con con
          | Case (locexp, arms) => Case (f locexp, subst_arms (pv, replacement) arms)
          | Fn (x, locexp) => if x = pv then Fn (x, locexp) else Fn (x, f locexp)
          | App (locexp1, locexp2) => App(f locexp1, f locexp2)
          | Conapp (con, locexp) => Conapp (con, f locexp)
          | Tuple locexps => Tuple (List.map f locexps)
          | Merge locexps => Merge (List.map f locexps)
          | RecordExp (fld, locexp) => RecordExp (fld, f locexp)
          | Proj (fld, locexp) => Proj (fld, f locexp)
          | Let (locdecs, locexp) => let in case subst_locdecs (pv, replacement) locdecs of
                                                                 (locdecs', shadowed) => Let (locdecs',
                                                                                                                    if shadowed then locexp else f locexp)
                                                    end
          | Lethint (annotation, locexp) => Lethint (annotation, f locexp)
          | Anno (locexp, annotation) => Anno (f locexp, annotation)
          | LET (lin, locexp, exp) => if lin = pv then LET (lin, f locexp, exp) else LET (lin, f locexp, subst (pv, replacement) exp)
          | LETSLACK (lin, locexp, exp) => if lin = pv then LETSLACK (lin, f locexp, exp) else LETSLACK (lin, f locexp, subst (pv, replacement) exp)
          | Lvar lin => if lin = pv then replacement else Lvar lin
          | Raise locexp => Raise (f locexp)
          | Handle (locexp1, pv', locexp2) => if pv = pv' then Handle (f locexp1, pv', locexp2) else Handle (f locexp1, pv', f locexp2)
          | Spy(spystuff, locexp) => Spy(spystuff, f locexp)
      end
  and subst_locexp (pv, replacement) (loc, exp) = (loc, subst (pv, replacement) exp)
  and subst_arms (pv, replacement) arms = List.map (subst_arm (pv, replacement)) arms
  and subst_arm (pv, replacement) (Arm(pattern, locexp)) = Arm(pattern, subst_locexp (pv, replacement) locexp)
  and subst_locdecs (pv, replacement) [] = ([], false (*not shadowed*))
    | subst_locdecs (pv, replacement) ((loc, Dec (d, kw, locexp)) :: rest) =
         let val locexp' = subst_locexp (pv, replacement) locexp
             val locdec' = (loc, Dec (d, kw, locexp'))
         in
              if d = pv then
                (locdec' :: rest  (* shadowed, so only substitute within this binding *),
                 true (*shadowed*) )
              else
                let val (decs, shadowed) = subst_locdecs (pv, replacement) rest
                in
                    (locdec' :: decs, shadowed)
                end
         end
    | subst_locdecs (pv, replacement) ((dec as (loc, (*XXX*) Local _)) :: rest) =
          let val (decs, shadowed) = subst_locdecs (pv, replacement) rest
          in 
              (dec :: decs, shadowed)
          end
    | subst_locdecs (pv, replacement) (dec :: rest) =
          let val (decs, shadowed) = subst_locdecs (pv, replacement) rest
          in 
              (dec :: decs, shadowed)
          end

  fun rename {from= pv1, to= pv2} exp =
      subst (pv1, Var pv2) exp

  fun rename_locexp {from= pv1, to= pv2} locexp =
      subst_locexp (pv1, Var pv2) locexp


  fun rename_locexp_mass list locexp = case list of
          [] => locexp
        | (x1, x2) :: list => 
              let val locexp = rename_locexp {from= x1,  to= x2} locexp
              in
                  rename_locexp_mass list locexp
              end

end
