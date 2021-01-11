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
(* File: Letnormal.sml
 * Author: Joshua Dunfield
 * Contents: Let-normal translation.
 *
 * Major changes:  Revised translation, 2006-05
 *)
signature LETNORMAL = sig
  type binding
  val harden : binding list * Sdml.exp -> Sdml.exp
  val translate_program : Sdml.program -> Sdml.program
end

structure Letnormal :> LETNORMAL = struct

  open Sdml
  open Location

  

  fun newlinear name = PV.fresh name
  fun newlin () = newlinear "xxL"
  fun newfromvar pv = newlinear (PV.toShortString pv)
  
  datatype binding =
      Up of pv * location * exp
    | Slack of pv * location * exp
(*    | Dn of pv * location * exp *)

  fun harden ([], e) = e
    | harden (Up(X,loc,exp)::bs, e) = LET(X, (loc, exp), harden(bs, e))
    | harden (Slack(X,loc,exp)::bs, e) = LETSLACK(X, (loc, exp), harden(bs, e))
(*    | harden (Dn(Xdn,loc,exp)::bs, e) = LETDN(Xdn, (loc, exp), harden(bs, e)) *)

  fun antivalue e = case e of
 (* PART 1. SYNTHESIZING FORMS: No synthesizing form is an anti-value. *)
      Const _ => false
    | Var _ => false
    | Con _ => false
    | App _ => false
    | Proj _ => false
    | Anno _ => false
    | Lvar _ => false

(* PART 2. CHECKED VALUES: No value is an anti-value. *)
    | Fn _ => false

(* PART 3. case, ETC.: These are always anti-values. *)
    | Case _ => true
    | Let _ => true
    | Lethint _ => true (* ??? *)
    | Raise _ => true
    | Handle _ => true

(* PART 4. CONTINGENT FORMS: Anti-valueness depends on subterms. *)
    | RecordExp (_, (_, e0)) => antivalue e0
    | Conapp (_, (_, e0)) => antivalue e0
    | Spy (_, (_, e0)) => antivalue e0
    | Leftanno (_, (_, e0)) => antivalue e0
    | Tuple exps => List.exists (antivalue o (fn (loc, exp) => exp)) exps

(* ???   MERGE *)
    | Merge exps => List.exists (antivalue o (fn (loc, exp) => exp)) exps

(* Should be impossible: *)
    | LET(_, (loc1, e1), e2) => raise Match (* antivalue e1 orelse antivalue e2 *)
    | LETSLACK(_, (loc1, e1), e2) => raise Match (* antivalue e1 orelse antivalue e2  *)

(* antivalue_split es  =  (esLeft, esRight), where either
    - If not (List.exists antivalue es),  then  esLeft = es  and esRight = [].   This is like the (\PreV, e2) case in the formal system.
    - If List.exists antivalue es, then with LAV=the *leftmost* antivalue in es, so es = es1 @ [LAV] @ es2,
             then esLeft = es1 @ [LAV] and esRight = es2.
*)
  fun antivalue_split [] = ([], [])
    | antivalue_split ((e1 as (loc1, exp1)) :: es) =
        if antivalue exp1 then
            ([e1], es)
        else
            let val (esLeft, esRight) = antivalue_split es
             in
                 (e1 :: esLeft, esRight)
             end

  fun translate (loc, exp) = (loc, harden (translate_locexp (loc, exp)))

  and translate_locexp (loc, exp) =   (* location * exp -> binding list * exp *)

      let in case exp of

          Const(texp, string) =>
              ([], Const(texp, string))

        | Var x =>
              let val X = newfromvar x in
                  ([Up(X, loc, Var x)],
                   Lvar X)
              end

        | Spy(stuff, (loc0, Var y)) => 
              let val Y = newfromvar y in
                  ([Up(Y, loc, Spy(stuff, (loc0, Var y)))],
                   Lvar Y)
              end

        | Con c => (* ([], Con c) *)   (* Huh?  This was wrong --- Con (which doesn't exist in the formal system) is treated
                                  as a synthesizing form by Sdml.sml:isSynth and by Typecheck.sml! *)
            let val C = newfromvar c in
                   ([Up(C, loc, Con c)],
                   Lvar C)
           end
(***
   (* Eta-expand *)
              let val argpv = PV.fresh "etaconL"
              in
                  ([],
                   Fn(argpv, (loc, Conapp(c, (loc, Var argpv)))))
              end
***)

        | Anno(e1 as (loc1, exp1), anno) => 
              let val (L1, M1) = translate_locexp e1
                  and X = newlinear "annoL"
                  and vartype = if isVal exp1 then Slack else Up
              in
                  (L1 @ [vartype(X, loc, Anno((loc1, M1), anno))],
                   Lvar X)
              end

        | Leftanno(leftanno, e1 as (loc1, exp1)) => 
              let val (L1, M1) = translate_locexp e1
                  and X = newlinear "leftannoL"
                  and vartype = Up
              in
                  (L1 @ [vartype(X, loc, Leftanno(leftanno, (loc1, M1)))],
                   Lvar X)
              end

        | Case(e1 as (loc1, _), ms) =>
              let val (L, e') = translate_locexp e1
                  val ms' = translate_arms ms
              in
                  (L,
                   Case((loc1, e'), ms'))
              end

        | Fn(x, e) => ([], Fn(x, translate e))

        | App(e1 as (loc1,exp1), e2 as (loc2,_)) =>
              let val (L1, M1) = translate_locexp e1
              in
                  if antivalue exp1 then
                      let val X = newlinear "appL"
                      in
                          (L1 @ [Up(X, loc, App((loc1, M1), translate e2))],
                           Lvar X)
                      end
                  else
                      let val (L2, M2) = translate_locexp e2
                          and X = newlinear "appL"
                      in
                          (L1 @ L2 @ [Up(X, loc, App((loc1, M1), (loc2, M2)))],
                           Lvar X)
                      end
              end

        | Conapp(c, e1 as (loc1,_)) => let val (L, M) = translate_locexp e1
                         in
                             (L,
                              Conapp(c, (loc1, M)))
                         end

        | RecordExp(fld, e1 as (loc1,_)) => let val (L, M) = translate_locexp e1
                         in
                             (L,
                              RecordExp(fld, (loc1, M)))
                         end

        | Tuple(es) =>
              let val (esLeft, esRight) = antivalue_split es
                  val LMs1 = List.map translate_locexp esLeft
                  val (Ls1, Ms1) = ListPair.unzip LMs1
                  val left = map (fn ((loc',_), M) => (loc', M)) (ListPair.zip (esLeft, Ms1))
                  val right = map translate esRight
              in
                  (List.concat Ls1,
                   Tuple(left @ right))
              end

        | Merge(es) =>
             ([], Merge (map translate es))

        | Proj(fld, e) => let val (L, M) = translate_locexp e
                            and X = newlinear ("proj" ^ fld ^ "L")
                        in
                            (L @ [Up(X, loc, Proj(fld, (loc, M)))],
                             Lvar X)
                        end

        | Lethint(anno, e1) =>
              ([],
               Lethint(anno, translate e1))

(* Let, like App and Tuple, is a sequencing construct, so it needs to distinguish pre- and anti-values.
  However, the TOPLEVEL_* variants are excluded (I no longer immediately recall why), and
  mutually recursive function declarations (the `decs as (_::_::_)' case below) are treated as
  \Fix{u} Tuple[...], which is not a value.  The only place where pre-values are possible (indeed,
  almost mandatory, since the let-bound expression must be a synthesizing form (unless there is
  some \Rcontra stuff going on, hence my `almost')) is in the actual `let'.

  (Recall that annotated checking forms are pre-values.)
 *)
        | Let([(loc, Dec(pv, kw, locexp as (loc1, exp1)))], e) =>
              if antivalue exp1 then   (* As discussed above, this case will be very rare. *)
                  ([],
                   Let([(loc, Dec(pv, kw, translate locexp))], translate e))
              else
                  let val (L1, M1) = translate_locexp locexp
                  in (L1,
                      Let([(loc, Dec(pv, kw, (loc1, M1)))], translate e))
                  end

        | Let(decs, e) =>    (* Block of (probably) mutually recursive function declarations *)
              let val decs' = map let in fn (loc, Dec(pv, kw, locexp as (loc2, _))) =>
                                                       let in
                                                           (loc, Dec(pv, kw, translate locexp))
                                                       end
                                                | (loc, other) => (loc, other) end
                                           decs
              in
                  ([],
                   Let(decs', translate e))
              end

        | Raise e => 
              let val X = newlinear "raiseL"
              in
                  ([Up(X, loc, Raise(translate e))],
                   Lvar X)
              end

        | Handle(e1 as (loc1, _), x, e2) =>
              let val (L, e') = translate_locexp e1
              in
                  (L,
                   Handle((loc1, e'), x, translate e2))
              end
(*        | Handle (e1, x, e2) => 
              let val Ydn = newlinear "handleL"
              in
                  (Dn(Ydn, loc, Handle(translate e1, x, translate e2))],
                   Dnvar Ydn)
              end
*)
      end

  and translate_arm (Arm(pattern, locexp)) = Arm(pattern, translate locexp)

  and translate_arms arms = map translate_arm arms

  and translate_dec (Dec(pv, kw, locexp)) = Dec(pv, kw, translate locexp)
    | translate_dec dec = dec

  fun translate_decs [] = []
    | translate_decs (d::ds) = (translate_dec d)::(translate_decs ds)

  fun translate_program (Program(template, typedecsl, locexp)) = 
      Program(template, typedecsl, translate locexp)
end
