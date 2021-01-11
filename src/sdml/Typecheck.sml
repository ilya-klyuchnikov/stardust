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
signature TYPECHECK = sig

  type result = Sdml.locexp
  
  val typecheck : Sdml.program
                  ->
                  {source: Sdml.program,
                   prelude: string,
                   elaboration: Sdml.program} option
                                 (* if typechecking failed, returns NONE *)
                                 (* if typechecking succeeded, returns SOME {source, elaboration, ...} *)
  
  val infer : result Context.failure
           -> Context.inference_disposition
           -> Context.ctx
           -> (Sdml.locexp * Context.pexp)
           -> (result Context.failure * Context.mctx * (Sdml.texp * result) -> result)
           -> result
  
  val check : result Context.failure
           -> Context.ctx
           -> (Sdml.locexp * Context.pexp)
           -> Sdml.texp
           -> (result Context.failure * Context.mctx * result -> result)
           -> result

  val check' : result Context.failure
           -> Context.ctx
           -> (Sdml.locexp * Context.pexp)
           -> Sdml.texp
           -> (result Context.failure * Context.mctx * result -> result)
           -> result
  
  val check_annotation : result Context.failure
                   -> Context.ctx 
                   -> Location.location
                   -> Sdml.annotation
                   -> (result Context.failure * Context.mctx * Sdml.texp -> result)
                   -> result
  
  val check_arms :
               result Context.failure
            -> Context.ctx
            -> Sdml.texp
            -> ((Sdml.arm * Context.parm) list * Sdml.arm list)
            -> Sdml.pattern (*list*)
            -> Sdml.texp
            -> Location.location
            -> (result Context.failure * Context.mctx * Sdml.arm list -> result)
            -> result
  
  val infer_decs : result Context.failure
                   -> Context.ctx
                   -> Location.location
                   -> (Sdml.locdec * Context.pdec) list
                   -> (result Context.failure * Context.ctx * Sdml.locdec list -> result)
                   -> result
  
  val inferConapp :
           result Context.failure
      -> Context.ctx
      -> Location.location
      -> PV.sym
      -> Sdml.texp
      -> (result Context.failure * Context.mctx * PV.sym(*conjunct*) * Sdml.texp * Sdml.texp (* * result *) -> result)
      -> result


   val refutations : int ref  
end



structure Typecheck :> TYPECHECK = struct
  fun PRINT x = print x
(*  val print = fn string => () *)
  val print = print
(*  val PRINT = print *)

  val refutations : int ref = ref 0

  open Silly
  open Sdml
  open Context
  open Subtype
  open Case
  structure AG = Agreement
  infix 5 %%
  infix 5 $+
  infix 5 ++
  infix 5 +-
  infix 5 +--+
  infix 5 +~~+

  type result = locexp

  fun refract k refractor =
      fn (failure, ctx, result) => k (failure, ctx, refractor result)

  fun inferrefract k refractor =
      fn (failure, ctx, (result1, result2)) => k (failure, ctx, (result1, refractor result2))

  structure CC = Sdml.ConcreteContext
  structure X = Indexing
  structure DS = Datasorts
  type constraint = X.constraint
  type state = Solve.state
  type disjuncts = Context.disjuncts

  
  structure IAE = IntStatistEnv
  structure PVAE = PVStatistEnv
  structure TCAE = TCStatistEnv
  structure P = Print
  structure PP = PrettyPrint
  
  val unionLeftCount : int ref = ref 0
  val sectLeftCount : int ref = ref 0
  val solveCount : int ref = ref 0
  val memoAdd : int ref = ref 0
  val memoHit : int ref = ref 0
  val memoLookup : int ref = ref 0
  val caseArmChecked : int ref = ref 0

  val check_pattern_now : int ref = ref 99
  val build_pattern_tracks_now : int ref = ref 99
  fun INC r = (r := !r + 1; !r)
  fun sINC r = Int.toString (INC r)

  val {dprint, dprnt} =
          Debug.register {full_name= "Typecheck",
                          short_name= "Typecheck"}
  val {dprint= adprint, dprnt= adprnt} =
          Debug.register {full_name= "Typecheck-A",
                          short_name= "Typecheck-A"}

  val (cdprint, cdprnt) = (Case.dprint, Case.dprnt)

  local
      val index = Option.valOf (Debug.from "Typecheck")
  in
      fun fail s =
          Debug.makeFail index s
  end

  fun COVER s = ()   (* unimplemented *)  
  
  fun pprint s = print (s() ^ "\n")

  fun tv2str tv = TV.toString tv
  fun extv2str tv = "'E" ^ Int.toString (TV.toInt tv)
  fun t2str texp = P.pTexp texp
  fun topt2str texp = case texp of NONE => "NONE" | SOME texp => P.pTexp texp

  fun shortstr e =
      let in case e of
          Const _ => "Const"
    | Var  pv => "Var " ^ PV.toString pv
    | Con  pv => "Con " ^ PV.toString pv
    | Lvar  pv => "Lvar " ^ PV.toString pv
    | Case   _ => "Case"
    | Fn(pv,_) => "Fn("^PV.toString pv ^",_)"
    | App    _ => "App"
    | RecordExp    _ => "RecordExp"
    | Conapp    _ => "Conapp"
    | Merge   _ => "Merge"
    | Tuple   _ => "Tuple"
    | Proj(n,_) => "Proj(" ^ n ^ ",_)"
    | Let    _ => "Let"
    | Lethint _ => "Lethint"
    | Anno   _ => "Anno"
    | LET(pv,_,_) => "LET("^PV.toString pv ^",...)"
    | LETSLACK(pv,_,_) => "LETSLACK("^PV.toString pv ^",...)"
    | Raise _ => "Raise"
    | Handle _ => "Handle"
    | Spy _ => "Spy"
      end

  fun disjunctity (Union (A, B)) = 1 + disjunctity A + disjunctity B
    | disjunctity (Runion (A, B)) = 1 + disjunctity A + disjunctity B
    | disjunctity _ = 0

  fun xlookup Empty pv' =
          NONE
    | xlookup (Ctx(pv, what, ctx)) pv' =
          if pv = pv' then SOME what else xlookup ctx pv'

(* XXX Bug:
 let val z = (z : (H::nat, HZ::nat, z:zipper(H+1, HZ) => ...)
 explodes -- is `z' being put into the context too early or something?
 (If changed to let val zzzzz = ..., it's fine.)
*)
  fun rlookup fullctx info Empty pv' =
      (* fail ("rlookup " ^ PV.toString pv' ^ " (" ^ info ^ " )" ^ rctxToString fullctx) *)
         (PRINT ("rlookup failed: " ^ PV.toString pv' ^ " (" ^ info ^ ") " ^ rctxToString fullctx ^ "\n");
          raise Context.LookupFailure (fn () => "rlookup " ^ PV.toString pv' ^ " (" ^ info ^ ") " ^ rctxToString fullctx))
    | rlookup fullctx info (Ctx(pv, what, ctx)) pv' =
          if pv = pv' then
              what
          else
              rlookup fullctx info ctx pv'

  fun rlookup_tc fullctx info Empty tc' = fail ("rlookup_tc " ^ TC.toString tc' ^ " (" ^ info ^ ") " ^ rctxToString fullctx)
    | rlookup_tc fullctx info (Ctx(tc, what, ctx)) tc' =
          if tc = tc' then what else rlookup_tc fullctx info ctx tc'

  fun mlookup fullctx info Empty pv' = fail ("mlookup " ^ PV.toString pv' ^ " (" ^ info ^ ") " ^ mctxToString fullctx)
    | mlookup fullctx info (Ctx(pv, what, ctx)) pv' =
          if pv = pv' then what else mlookup fullctx info ctx pv'

  
  fun lookupConinfo info rctx c =
      rlookup rctx ("Con--" ^ info) (getCon rctx) c

  fun lookupTypeinfo rctx tc =
      rlookup_tc rctx ("") (getTypes rctx) tc

  fun lookupSorting rctx tc =
       (if TC.toShortString tc = "bits" then
           print ("lookupSorting bits: rctx is " ^ rctxToString rctx ^ "\n")
        else ();
        case xlookup (getTypes rctx) (DS.blitheRefines tc) of
            SOME (Typeinfo{indexsort, ...}) => SOME indexsort
          | NONE => NONE
       )

  fun lookupConjuncts info rctx c =
      case lookupConinfo info rctx c of
          Coninfo{conjuncts, ...} => conjuncts

  fun lookupContype info rctx c =
      case lookupConinfo info rctx c of
          Coninfo{contype, ...} => contype

  fun lookupOrd info mctx pv =
      D.lookupOrdinary pv (getG mctx) ("Ord--"^info)

  fun lookupLinear info mctx pv =
      ( (*PRINT ("lookupLinear: " ^ PV.toString pv ^ " in " ^ mctxToString mctx ^ "\n"); *)
       D.lookupLinear pv (getG mctx) ("Linear--"^info)
      )

  fun lookupSlack info mctx pv =
      let in
          D.lookupSlack pv (getG mctx) ("Slack--"^info)
      end
      handle 
         Context.LookupFailure stuff =>
             raise Context.LookupFailure stuff

  fun lookupUnivType info mctx tv =
      D.lookupUnivType tv (getG mctx) ("Tyvars--"^info)

  fun getTyvar mctx tv = case lookupUnivType "" mctx tv of
     NONE => Typevar tv
   | SOME A => (print "~"; A)

  fun lookupType info rctx tc = rlookup_tc rctx ("Types--"^info) (getTypes rctx) tc
  
(*  fun setLinearEmpty rctx = updateLinear rctx (fn oldLinear => Empty)
*)

  fun varInSlack mctx pv =
      (let val _ = lookupSlack "" mctx pv
       in
           true
       end)
      handle  _ => false

(*****
                      fun mixfail whichFn pv' assn desired =
                          let val assnStr = case assn of
                              Vr _ => "Vr" 
                              | Tyvars _ => "Tyvars" 
                              | Slack _ => "Slack" 
                              | Contype _ => "Contype" 
                          in
                              fail ("disastrous " ^ whichFn ^ "failure: death by mixing: symbol " ^ PV.toString pv' ^ " -- wanted" ^ desired ^ " but got " ^ assnStr)
                          end
*****)
  
  fun mapBarrierIDs mctx barrierIDMap =
      let val barrierIDMap = map (fn (a, b) => (b, a)) barrierIDMap
          fun f (Barrier id) =
              Barrier (case Assoc.getOpt barrierIDMap id of
                           NONE => id
                         | SOME id' => id')
            | f assn = assn
       in
          updateIndex mctx (fn index => map f index)
      end

  exception AllDead of mctx * (unit -> string)

  exception Dead of mctx * (unit -> string)

  fun XXraise_Dead mctx why = ( dprint ((fn () => "*** "^why()(*^"   --- " ^ pathToString path ^""*)) );
                                                     recentPaths := (getPath mctx) :: (!recentPaths);
                            raise Dead (mctx, why))
  fun raise_Dead failure mctx why = ( dprint ((fn () => "*** "^why()(*^"   --- " ^ pathToString path ^""*)));
                                                     recentPaths := (getPath mctx) :: (!recentPaths);
                            failure (mctx, why))
  fun raiseDead' failure mctx loc why = raise_Dead failure mctx (fn () => why() ^ " @ " ^ Location.toString loc)
  fun raise_AllDead mctx why = let val path = getPath mctx in ( PRINT ("\n*** "^why()^"\n" ^ pathToString path ^ "\n");
                                                                recentPaths := path :: (!recentPaths);
                                                                raise AllDead (mctx, why))
                                                  end
  fun raiseAllDead' mctx loc why = raise_AllDead mctx (fn () => why() ^ " @ " ^ Location.toString loc)
  fun raiseAllDead mctx loc why = raise_AllDead mctx (fn () => why ^ " @ " ^ Location.toString loc)


  fun failloc loc why = fail (why ^ " @ " ^ Location.toString loc)

  fun redalert_x x = if PV.toInt x = 47 then print "\n\nRED ALERT! RED ALERT!\n\n\n" else ()
  fun redalert e =
      case e of 
          Proj (k, (loc, e)) => redalert e
        | Var x => redalert_x x
        | Lvar x => redalert_x x
        | _ => ()

  fun redalert_Proj (n, e) =
      (redalert (Proj (n, e));
       Proj (n, e))

  datatype trackinfo =
           IALL of IndexSym.sym * X.sort
         | ITYPEVAR of TV.sym

  structure Track = struct
    datatype track =
        And of track list
      | Req of requirement * track
      | Supp of supp * track
      | End of mctx
    and requirement =
        Subtype of texp * texp
      | Prop of constraint
    and supp =
        Binding of pv * texp
      | Index of indexassumption list

(*
    fun append dropIn track =
        let val append = append dropIn
        in
            case track of
                And ts => And (map append ts)
              | Req (req, t) => Req (req, append t)
              | Supp (supp, t) => Supp (supp, append t)
              | End => dropIn
        end
*)
    fun reqToString req = case req of
      Subtype(t1, t2) => "(" ^ t2str t1 ^ " <= " ^ t2str t2 ^ ")"
    | Prop P => "{" ^ X.Constraint.toString P ^ "}"
    
    fun suppToString supp = case supp of
      Binding(x, A) => "(" ^ PV.toShortString x ^ " : " ^ t2str A ^ ")"
    | Index index => "(" ^ indexToString index ^ ")"
    
    fun toString track =
        case track of
            And ts => Separate.list "\nAnd  " (map toString ts)
          | Req (req, t) => "Req(" ^ reqToString req ^ "   " ^ toString t ^ ")"
          | Supp (supp, t) => "Supp(" ^ suppToString supp ^ "   " ^ toString t ^ ")"
          | End _ => "End _"
    
    fun mkReq (Prop X.TRUE, track) = track
      | mkReq (req, track) = Req(req, track)
    
    fun mkSupp (Index [], track) = track
      | mkSupp (supp, track) = Supp(supp, track)
  end
  structure T = Track


  fun currymap f xs ys =
      ListPair.map (fn (x, y) => f x y) (xs, ys)

  fun curryapp f xs ys =
      ListPair.app (fn (x, y) => f x y) (xs, ys)

  exception Overlay

  val ren : (pv * pv) list ref = ref []
  
  fun relate (loc1, exp1 : exp) (loc2, exp2 : exp) =
      relate_exp exp1 exp2
      
  and relate_texp t1 t2 =
      t1 (* XXX*)
  
  and relate_string s1 s2 = ()
  and relate_pv x1 x2 =
             if x1 = x2 then ()
             else 
                 ren := (x2, x1) :: (!ren)

  and relate_tc s1 s2 = ()
  
  and relate_exp exp1 exp2 =
      let
          val _ = dprint (fn () => "relate_exp {   " ^ Print.pExp exp1 ^ "     +with+     " ^Print.pExp exp2)
      in
          case (exp1, exp2) of
             (Const (t1, s1),  Const (t2, s2)) => 
                 (relate_texp t1 t2;
                  relate_string s1 s2)
           | (Var v1, Var v2) => ()  (* (relate_pv v1 v2) *)
           | (Con v1, Con v2) => () (* (relate_pv v1 v2) XXX *)
           | (Fn(x1, e1), Fn(x2, e2)) =>
                 (relate_pv x1 x2;
                  relate e1 e2)
           | (App (f1, a1),  App (f2, a2)) => 
                 (relate f1 f2;
                  relate a1 a2)
           | (Conapp (f1, a1),  Conapp (f2, a2)) => 
                 relate a1 a2
           | (RecordExp (s1, e1),  RecordExp (s2, e2)) => 
                 relate e1 e2
           | (Tuple es1,  Tuple es2) =>
                 relate_s es1 es2
           | (Merge es1,  Merge es2) => 
                 relate_s es1 es2
           | (Proj (k1, e1),  Proj (k2, e2)) => 
                (relate_string k1 k2;
                 relate e1 e2)
           | (Let (decs1, e1),  Let (decs2, e2)) => 
                (relate_decs decs1 decs2;
                 relate e1 e2)
           | (Lethint (annotation1, e1),  Lethint (annotation2, e2)) => 
                 relate e1 e2
           | (Anno (e1, anno1),  Anno (e2, anno2)) => 
                 relate e1 e2
           | (LET (x1, e1, body1),  LET (x2, e2, body2)) => 
                 (relate_pv x1 x2;
                  relate e1 e2;
                  relate_exp body1 body2)
           | (LETSLACK (x1, e1, body1),  LETSLACK (x2, e2, body2)) => 
                 (relate_pv x1 x2;
                  relate e1 e2;
                  relate_exp body1 body2)
           | (Lvar x1,  Lvar x2) => 
                  ()
           | (Raise e1,  Raise e2) => 
                  relate e1 e2
           | (Handle (e1, x1, handler1),  Handle (e2, x2, handler2)) => 
                 (relate e1 e2;
                  relate_pv x1 x2;
                  relate handler1 handler2)
           | (Spy (spy1, e1),  Spy (spy2, e2)) => 
                 relate e1 e2
           | (Leftanno (leftanno1, e1),  Leftanno (leftanno2, e2)) => 
                 relate e1 e2

           | (Case (e1, arms1),  Case (e2, arms2))  => 
                 (relate e1 e2;
                  relate_arms [] arms1 arms2)

           | (_, _) => 
                 raise Overlay
      end

  and relate_s (es1 : locexp list) es2 =
      curryapp relate es1 es2

  and relate_exps (es1 : exp list) es2 =
      curryapp relate_exp es1 es2

  and relate_pattern' p1 p2 = case (p1, p2) of
       (VarPattern x1, VarPattern x2) =>
            ren := (x2, x1) :: (!ren)
     | (WildPattern, WildPattern) => ()
     | (OrPattern pats1, OrPattern pats2) =>
            relate_patterns' pats1 pats2
     | (CtorPattern (c1, patOpt1),  CtorPattern (c2, patOpt2)) => 
            if c1 <> c2 then
                raise Overlay
            else
                relate_patternOpt' patOpt1 patOpt2
     | (RecordPattern (s1, p1),  RecordPattern (s2, p2)) => 
            if s1 <> s2 then
                raise Overlay
            else
                relate_pattern p1 p2
     | (TuplePattern ps1,  TuplePattern ps2) => 
            relate_patterns' ps1 ps2
     | (AsPattern (x1, p1),  AsPattern (x2, p2)) => 
            (ren := (x2, x1) :: (!ren);
             relate_pattern' p1 p2)
     | (StringPattern s1,  StringPattern s2) => 
            if s1 <> s2 then
                raise Overlay
            else ()
     | (IntPattern s1,  IntPattern s2) => 
            if s1 <> s2 then
                raise Overlay
            else ()
     | (_, _) =>
            raise Overlay

  and relate_patternOpt' patOpt1 patOpt2 = case (patOpt1, patOpt2) of
       (NONE, NONE) => ()
     | (SOME p1, SOME p2) => relate_pattern' p1 p2
     | (_, _) => raise Overlay

  and relate_patterns' ps1 ps2 =  (* XXX XXX XXX *)
      curryapp relate_pattern' ps2 ps2

  and relate_pattern p1 p2 =
      let val saved_ren = !ren
      in
          let in 
              relate_pattern' p1 p2
          end
          handle
             Overlay =>
                 ren := saved_ren
      end

  and relate_arms acc armsOne armsTwo =
      let
          fun take_prefix prefix p arms = case arms of
              [] => NONE
            | (arm as Arm (p2, _)) :: arms => 
                  if p = p2 then
                      SOME (prefix, arm, arms)
                  else
                      take_prefix (prefix @ [arm]) p arms
      in
          case (armsOne, armsTwo) of
               ([], []) => ()
             | ([], arms2) => ()
             | (Arm (pat1, e1) :: arms1,  arms2) =>
                   let in case take_prefix [] pat1 arms2 of
                              NONE =>
                                  let val acc = acc @ [Arm (pat1, e1)]
                                  in
                                      relate_arms acc arms1 arms2
                                  end
                            | SOME (prefix, Arm (pat2, e2), rest2) =>
                                  let val _ = relate_pattern pat1 pat2
                                      val _ = relate e1 e2
                                      val acc = acc @ prefix
                                  in
                                      relate_arms acc arms1 rest2
                                  end
                   end
      end


  and relate_decs decs1 decs2 =
      curryapp relate_locdec decs1 decs2

  and relate_decslist (decslist1 : locdec list list) decslist2 =
      curryapp relate_decs decslist1 decslist2

  and relate_locdec (loc1, dec1) (loc2, dec2) =
      relate_dec dec1 dec2
      
  and relate_dec dec1 dec2 = case (dec1, dec2) of
       (Dec (x1, kw1, e1),  Dec (x2, kw2, e2)) =>
            (relate_pv x1 x2;
             relate e1 e2)
     | (Typedec typedecs1,  Typedec typedecs2)  =>
            ()
     | (ValType (x1, dectype1),  ValType (x2, dectype2)) => 
            ()
      | (Datacon (c1, texp1),  Datacon (c2, texp2)) =>
            ()
      | (TyvarVariance (tv1, variance1),  TyvarVariance (tv2, variance2)) =>
            ()
      | (DatatypeWith (tc1, sorting1),  DatatypeWith (tc2, sorting2)) =>
            ()
      | (Local (locdecs1, locdecs1'),  Local (locdecs2, locdecs2')) =>
            (relate_decslist locdecs1 locdecs2;
             relate_decslist locdecs1' locdecs2')
      | (TestSubtype (sense1, (A1, B1)),  TestSubtype (sense2, (A2, B2))) =>
            ()

       | (_, _) => 
             raise Overlay







  fun eq s1 eqf s2 =
      if eqf (s1, s2) then s1
      else raise Overlay

  fun overlay (loc1, exp1 : exp) (loc2, exp2 : exp) =
      (loc1, overlay_exp exp1 exp2)
      
  and overlay_texp t1 t2 =
      t1 (* XXX*)
  
  and overlay_string s1 s2 = eq s1 (op=) s2
  and overlay_pv s1 s2 = eq s1 (op=) s2
  and overlay_tc s1 s2 = eq s1 (op=) s2
  
  and overlay_exp exp1 exp2 =
      let
          val _ = dprint (fn () => "overlay_exp {   " ^ Print.pExp exp1 ^ "     +with+     " ^Print.pExp exp2 ^ "}")
      in
          case (exp1, exp2) of
             (Const (t1, s1),  Const (t2, s2)) => 
                 Const (overlay_texp t1 t2,
                        overlay_string s1 s2)
           | (Var v1, Var v2) => Var (overlay_pv v1 v2)
           | (Con v1, Con v2) => Con (overlay_pv v1 v2)
           | (Fn(x1, e1), Fn(x2, e2)) =>
                 Fn(x1, overlay e1 e2)
           | (App (f1, a1),  App (f2, a2)) => 
                 App (f1, overlay a1 a2)
           | (Conapp (f1, a1),  Conapp (f2, a2)) => 
                 Conapp (f1, overlay a1 a2)
           | (RecordExp (s1, e1),  RecordExp (s2, e2)) => 
                 RecordExp (overlay_string s1 s2,
                            overlay e1 e2)
           | (Tuple es1,  Tuple es2) =>
                 Tuple (overlay_s es1 es2)
           | (Merge es1,  Merge es2) => 
                 Merge (overlay_s es1 es2)
           | (Proj (k1, e1),  Proj (k2, e2)) => 
                 redalert_Proj (overlay_string k1 k2,
                       overlay e1 e2)
           | (Let (decs1, e1),  Let (decs2, e2)) => 
                 Let (overlay_decs decs1 decs2,
                      overlay e1 e2)
           | (Lethint (annotation1, e1),  Lethint (annotation2, e2)) => 
                 Lethint (annotation1, overlay e1 e2) (* XXX *)
           | (Anno (e1, anno1),  Anno (e2, anno2)) => 
                 Anno (overlay e1 e2, anno1) (* XXX *)
           | (LET (x1, e1, body1),  LET (x2, e2, body2)) => 
                 LET (x1, overlay e1 e2, overlay_exp body1 body2)
           | (LETSLACK (x1, e1, body1),  LETSLACK (x2, e2, body2)) => 
                 LETSLACK (x1, overlay e1 e2, overlay_exp body1 body2)
           | (Lvar x1,  Lvar x2) => 
                 Lvar x1
           | (Raise e1,  Raise e2) => 
                 Raise (overlay e1 e2)
           | (Handle (e1, x1, handler1),  Handle (e2, x2, handler2)) => 
                 Handle (overlay e1 e2, x1, overlay handler1 handler2)
           | (Spy (spy1, e1),  Spy (spy2, e2)) => 
                 Spy (spy1(*XXX*), overlay e1 e2)

           | (Leftanno (leftanno1, e1),  Leftanno (leftanno2, e2)) => 
                 Leftanno (leftanno1(*XXX*), overlay e1 e2)

           | (Case (e1, arms1),  Case (e2, arms2))  => 
                 Case (overlay e1 e2, overlay_arms [] arms1 arms2)

           | (_, _) => 
                 raise Overlay
      end

  and overlay_s (es1 : locexp list) es2 =
      currymap overlay es1 es2

  and overlay_exps (es1 : exp list) es2 =
      currymap overlay_exp es1 es2

  and overlay_arms acc armsOne armsTwo =
      let
          fun take_prefix prefix p arms = case arms of
              [] => NONE
            | (arm as Arm (p2, _)) :: arms => 
                  if p = p2 then
                      SOME (prefix, arm, arms)
                  else
                      let val _ = dprint (fn () => "overlay_arms: preserving case arm "
                                         ^ Print.p Print.printArm arm)
                      in
                          take_prefix (prefix @ [arm]) p arms
                      end
      in
          case (armsOne, armsTwo) of
               ([], []) => acc
             | (arms1, []) => acc @ arms1
             | ([], arms2) => acc @ arms2
             | (Arm (pat1, e1) :: arms1,  arms2) =>
                   let in case take_prefix [] pat1 arms2 of
                              NONE =>
                                  let val acc = acc @ [Arm (pat1, e1)]
                                  in
                                      overlay_arms acc arms1 arms2
                                  end
                            | SOME (prefix, Arm (pat2, e2), rest2) =>
                                  let val overlaid_arm = Arm (pat1, overlay e1 e2)
                                      val acc = acc @ prefix @ [overlaid_arm]
                                  in
                                      overlay_arms acc arms1 rest2
                                  end
                   end
      end


  and overlay_decs decs1 decs2 =
      currymap overlay_locdec decs1 decs2

  and overlay_decslist (decslist1 : locdec list list) decslist2 =
      currymap overlay_decs decslist1 decslist2

  and overlay_locdec (loc1, dec1) (loc2, dec2) =
      (loc1, overlay_dec dec1 dec2)
      
  and overlay_dec dec1 dec2 = case (dec1, dec2) of
       (Dec (x1, kw1, e1),  Dec (x2, kw2, e2)) =>
            Dec (x1, kw1, overlay e1 e2)
     | (Typedec typedecs1,  Typedec typedecs2)  =>
            Typedec (typedecs1) (* XXX *)
     | (ValType (x1, dectype1),  ValType (x2, dectype2)) => 
            ValType (x1, dectype1) (* XXX *)
      | (Datacon (c1, texp1),  Datacon (c2, texp2)) =>
            Datacon (c1, texp1) (* XXX*)
      | (TyvarVariance (tv1, variance1),  TyvarVariance (tv2, variance2)) =>
            TyvarVariance (tv1, variance1) (* XXX*)
      | (DatatypeWith (tc1, sorting1),  DatatypeWith (tc2, sorting2)) =>
            DatatypeWith (tc1, sorting1) (* XXX*)
      | (Local (locdecs1, locdecs1'),  Local (locdecs2, locdecs2')) =>
            Local (overlay_decslist locdecs1 locdecs2,
                   overlay_decslist locdecs1' locdecs2')
      | (TestSubtype (sense1, (A1, B1)),  TestSubtype (sense2, (A2, B2))) =>
            TestSubtype (sense1, (A1, B1)) (* XXX*)

       | (_, _) => 
             raise Overlay

  local
      fun hit x = Assoc.apply (!ren) x

    (* rbo = replace bindings and occurrences *)
      fun rbo_pattern p = case p of
          VarPattern v => VarPattern (hit v)
        | WildPattern => WildPattern
        | OrPattern ps => OrPattern (List.map rbo_pattern ps)
        | CtorPattern (c, p0opt) => CtorPattern (c, Option.map rbo_pattern p0opt)
        | RecordPattern (s1, p0) => RecordPattern (s1, rbo_pattern p0)
        | TuplePattern ps => TuplePattern (List.map rbo_pattern ps)
        | AsPattern (x, p0) => AsPattern (hit x, rbo_pattern p0)
        | StringPattern s => StringPattern s
        | IntPattern n => IntPattern n

      fun rbo_exp e = case e of
          Var x => Var (hit x)
        | Lvar x => Lvar (hit x)
        | Fn (x, body) => Fn (hit x, body)
        | e => e

      fun rbo_arm (Arm (p, e)) =
          Arm (rbo_pattern p, e)

      val spec = SdmlFold.compose (SdmlFold.expSpec rbo_exp) (SdmlFold.armSpec rbo_arm)
  in
    val overlay =
       fn e1 => fn e2 =>
          (ren := [];
           relate e1 e2;
           let val e2 = SdmlFold.fold_locexp spec e2
           in
               overlay e1 e2
           end)
  end





  fun elaborateType (rctx, mctx) A =
      let val self = elaborateType (rctx, mctx)
      in
           case A of
            Typevar tv => Typevar tv
          | Extypevar tv => Extypevar tv    (* XXX *)
          | All (tv, universe, A0) => self A0   (* ??? *)

          | Arrow(dom, cod) => Arrow(self dom, self cod)
          | Product As => Product (List.map self As)

          | Tycon (tc, indexing, instantiation) =>
                let 
                    (* Elaborate to unrefined tc *)
                    val base_tc =
                        case Datasorts.refines tc of
                            NONE => tc
                          | SOME base_tc => base_tc
                in
                    Tycon (base_tc, X.N, List.map self instantiation)
                end

          | Record (field, A0) => (* Record *) ( (*field, *) self A0)

          | Top => Product []
          | Bot => Bot   (* XXX *)

          | Sect (A1, A2) => Product [self A1, self A2]
          | Union (A1, A2) => Tycon (#sumTC (Context.getDistinguished rctx), X.N, [self A1, self A2])

          | Rsect (A1, A2) => self A1
          | Runion (A1, A2) => self A1
          | Univ (a, sort, A0) => self A0
          | Exis (a, sort, A0) => self A0
          | Implies (constraint, A0) => self A0
          | Conj (constraint, A0) => self A0
      end

 (* mlify_constructor_type:
      Remove type quantifiers and change their bound variables to something matching the given `tvs'.
  *) 
  fun mlify_constructor_type tvs A =
      let fun get_codomain A =
              let
                  (* val _ = print ("get_codomain (" ^ t2str A ^ ")\n") *)
              in case A of
                    Typevar tv => raise Option
                  | Extypevar tv => raise Option
                  | All (tv, universe, A0) =>
                         get_codomain A0

                  | Arrow (dom, cod) => get_codomain cod
                  | Product As => raise Option
                  | Tycon (tc, indexing, instantiation) => A

                  | Record (field, A0) => raise Option

                  | Top => raise Option
                  | Bot => raise Option
                  
                  | Sect (A1, A2) => get_codomain A1
                  | Union (A1, A2) => raise Option
                  | Rsect (A1, A2) => get_codomain A1
                  | Runion (A1, A2) => raise Option
                  
                  | Univ (a, sort, A0) => get_codomain A0
                  | Exis (a, sort, A0) => get_codomain A0
                  | Implies (constraint, A0) => get_codomain A0
                  | Conj (constraint, A0) => get_codomain A0
              end

          fun mk_assoc codomain = case codomain of
             Tycon(tc, indexing, instantiation) => 
                   let val instantiation_tvs = List.mapPartial (fn Typevar tv' => SOME tv' | _ => NONE) instantiation
                   in
                       ListPair.zip (instantiation_tvs, List.map Typevar tvs)
                   end
          
          fun strip_quantifiers assoc A =              
              let val self = strip_quantifiers assoc
                  val stripped =
                           case A of
                               Typevar tv => A
                             | Extypevar tv => A
                             | All (tv, universe, A0) =>
                                     let in
                                         case Assoc.getOpt assoc tv of
                                             NONE => (print ("WARNING: `too much' polymorphism in constructor type; SML output may be ill-formed\n"); A)
                                           | SOME _ => self A0
                                     end

                             | Arrow(dom, cod) => Arrow(self dom, self cod)
                             | Product As => Product (List.map self As)
                             | Tycon (tc, indexing, instantiation) => A
                             
                             | Record (field, A0) => Record (field, self A0)

                             | Sect (A1, A2) => Sect (self A1, self A2)
                             | Union (A1, A2) => Union (self A1, self A2)
                             | Rsect (A1, A2) => Rsect (self A1, self A2)
                             | Runion (A1, A2) => Runion (self A1, self A2)
                             | Univ (a, sort, A0) => Univ (a, sort, self A0)
                             | Exis (a, sort, A0) => Exis (a, sort, self A0)
                             | Top => A
                             | Bot => A
                             | Implies (constraint, A0) => Implies (constraint, self A0)
                             | Conj (constraint, A0) => Conj (constraint, self A0)
              in
                  Types.substTypevar assoc stripped 
              end

          val codomain = get_codomain A
          val assoc = mk_assoc codomain
          val stripped = strip_quantifiers assoc A
      in
          Types.substTypevar assoc stripped
      end


  fun uncurry2 f (x, y) = f x y
  fun refinedBy basetype contype =
          let
(*                val _ = print ("basetype: " ^ t2str basetype ^ "\n" ^ "contype: " ^ t2str contype ^ "\n") *)
              val result = case (basetype, contype) of
              (Arrow(A1, B1), Arrow(A2, B2)) => (refinedBy A1 A2) andalso (refinedBy B1 B2)
            | (Typevar tv1, B) => true      (* COMMENT THIS ARM TO TURN OFF GADTs *)
(*              | (Typevar tv1, Typevar tv2) => (tv1 = tv2) (* UNCOMMENT THIS ARM WHEN TURNING ON(OFF??) GADTs *) *)
            | (A, All(beta, uu, B0)) => refinedBy A B0
            | (Product As, Product Bs) =>
                     let in
                         (List.all (fn (A,B) => refinedBy A B) (ListPair.zip (As, Bs)))
                         handle _ => false
                     end
            | (Tycon (tc1, X.N, texps1), Tycon(tc2, _, texps2)) =>
(*THIS DISABLES GADTs:                     (texps1 = texps2)  (*PPP*) (*XXX*)
*) (* THE  FOLLOWING ENABLES GADTs:  ?????*)
                    (List.length texps1 = List.length texps2)
                 andalso 
                    (List.all (uncurry2 refinedBy) (ListPair.zip (texps1, texps2)))
                 andalso
                    (tc1=tc2 orelse DS.blitheSubsort (tc2, tc1))
            | (basetype, Sect(B1, B2)) => (refinedBy basetype B1) andalso (refinedBy basetype B2)
            | (basetype, Union(B1, B2)) => (refinedBy basetype B1) andalso (refinedBy basetype B2)

            | (basetype, Rsect(B1, B2)) => (refinedBy basetype B1) andalso (refinedBy basetype B2)
            | (basetype, Runion(B1, B2)) => (refinedBy basetype B1) andalso (refinedBy basetype B2)

            | (basetype, Univ(b, sort, B)) => refinedBy basetype B
            | (basetype, Exis(b, sort, B)) => refinedBy basetype B
            | (basetype, Implies(P, B)) => refinedBy basetype B
            | (basetype, Conj(P, B)) => refinedBy basetype B
            | (Top, _) => true
            | (_, Bot) => true  (* ??? *)
            | (_, _) => false
(*                val _ = print ("result: " ^ Bool.toString result ^ "\n") *)
          in
              result
          end

(* good acc datatexp contype:

          nullary        NONE = unknown,  SOME true = nullary,  SOME false = not nullary
          acc              Conjuncts so far
          enclosure    Function to recreate quantifiers, etc. that we've gone inside
          datatexp     The "raw" datatype, i.e. Tycon(...)
          contype       The declared constructor type, e.g. an intersection of Arrow(..., Tycon(...))
*)
  fun good (nullary : bool option, acc : texp list, enclosure : texp -> texp) datatexp contype =
      let in case contype of
           Sect (A1, A2) =>  (* non-refinement intersections not allowed on heads of constructors *)
                NONE
         | Rsect (A1, A2) =>
                let in case good (nullary, acc, enclosure) datatexp A1 of
                           NONE => NONE
                         | SOME (nullary, acc) => 
                              good (SOME nullary, acc, enclosure) datatexp A2
                end
(*
        | (Arrow(B1, B2), Arrow(A1, A2 as Tycon(A2tc, _, texps))) =>
              (refinedBy B1 A1) andalso (refinedBy B2 A2)
*)
        | All (a, universe, A) => good (nullary, acc, fn C => enclosure (All (a(*XXX*), universe, C))) datatexp A
        | Univ (a, sort, A) => good (nullary, acc, fn C => enclosure (Univ (a(*XXX*), sort, C))) datatexp A
        | Implies (P, A) => good (nullary, acc, fn C => enclosure (Implies (P, C))) datatexp A
        | Arrow (A1, A2) =>
              let in case nullary of
                         SOME true => NONE  (* mix of nullary and non-nullary *)
                       |_ (*NONE | SOME false*) => 
                            (* A1 can be anything *)
                                if refinedBy datatexp A2 then
                                       (* SOME (false, acc @ [enclosure (Arrow(A1, A2))]) *)
                                    SOME (false, acc @ [enclosure (Arrow(A1, A2))])
                                else
                                    NONE
              end
        | contype => 
              let in case nullary of
                         SOME false => NONE  (* mix of nullary and non-nullary *)
                       |_ (*NONE | SOME true*) => 
                            (* A1 can be anything *)
                                if refinedBy datatexp contype then
                                    SOME (true, acc @ [enclosure contype])
                                else
                                    NONE
              end
      end

  val good' = good : (bool option * texp list * (texp -> texp) -> texp -> texp -> (bool * texp list) option)

  fun good datatexp contype = good' (NONE, [], fn A => A) datatexp contype
  val good_making_conjunct_list = good : texp -> texp -> (bool * texp list) option
  
  fun good datatexp contype =
      let in case good_making_conjunct_list datatexp contype of
            NONE => NONE
          | SOME (bool, conjunct_list) =>
                (* conjunct list must be non-empty *)
                let val conjunct = List.foldr Rsect (List.hd conjunct_list) (List.tl conjunct_list)
                in
                    SOME (bool, [conjunct])
                end
      end
  
(* typedecsl, typedecs, cons, con *)
   (* Noise *)


(* TODO: pass loc to typecheck_typedecs* functions *)
    fun typecheck_typedecsl datacons (ctx : ctx) [] = (ctx, [], [])
      | typecheck_typedecsl datacons ctx (typedecs::typedecsl) =
        let val (ctx', typedecs', elabTypedecs) = typecheck_typedecs datacons ctx typedecs
            val (ctx'', typedecsl', elabTypedecsl) = typecheck_typedecsl datacons ctx' typedecsl
        in
            (ctx'', typedecs'::typedecsl', elabTypedecs::elabTypedecsl)
        end
    
    and typecheck_typedecs datacons ctx typedecs =
        let fun infer_typedecs ctx [] = (ctx, [])
              | infer_typedecs ctx (typedec::typedecs) =
                    let val (ctx, elabTypedec) = typecheck_typedec datacons ctx typedec
                        val (ctx', typedecs') = infer_typedecs ctx typedecs
                    in
                        (ctx', elabTypedec :: typedecs')
                    end

           val typedecs' = typedecs
           val (ctx', elabTypedecs) = infer_typedecs ctx typedecs
        in
            (ctx', typedecs', elabTypedecs)
        end
    
    and typecheck_typedec datacons (rctx, mctx) (Datatype {tc, builtin, params, sorting, constructors}) =
            let
                val tvs = List.map (fn Tvinfo(tv, variance) => tv) params
                val tvs_as_types = List.map (fn tv => Typevar tv) tvs

                val locally_defined_cons = datacons

                val unquant_D = Tycon(tc, X.N, tvs_as_types)
    (*            val D = Sdml.quantifyCtype unquant_D params *)

                (* val _ = print ("typecheck_typedec: length of datacons = " ^ Int.toString (List.length datacons) ^ "\n") *)

                (* add guards to a constructor type, to reflect subset sorts in the constructed datatype's sorting *)
                fun add_guards_sort sort contype = case sort of
                     X.Base _ => contype
                   | X.Product list => add_guards_list list contype
                   | X.List sort => add_guards_sort sort contype (* XXX *)
                   | X.Subset (sort, sym, constraint) =>
                         (* XXX *) (* XXX *)
                         add_guards_sort sort contype

                and add_guards_list [] contype = contype
                  | add_guards_list (sort :: rest) contype =
                       add_guards_sort sort (add_guards_list rest contype)

                fun add_guards sorting contype = case sorting of
                     X.Sorting.None => contype
                   | X.Sorting.Nameless (sort, _) => add_guards_sort sort contype
                   | X.Sorting.Fields list => add_guards_list (List.map (fn (fieldname, (sort, _)) => sort) list) contype


                fun is_my_con (Datacon (pv, A)) =
                          let 
                            val _ = dprint (fn () => "is_my_con: good/refinedBy(" ^ t2str unquant_D ^ ", " ^ t2str A ^ ")")
                            val result = case good unquant_D A of
                                                    SOME (nullary, conjuncts) =>
                                                        let val contype = Inject.clean (add_guards sorting A)
                                                            val _ = dprint (fn () => "  << adding " ^ PV.toString pv ^ " : " ^ t2str contype ^ " >>  ")
                                                            fun newFn () =
                                                                if builtin then
                                                                    PV.sanitary_fresh (PV.proper_name pv) (PV.toString pv)
                                                                else
                                                                    PV.new pv
                                                            val conjuncts_with_pvs = List.map (fn Ak => (newFn(), Ak)) conjuncts
                                                            (* val _ = print ("conjuncts_with_pvs = " ^ Separate.list " //\\\\ " (List.map (fn (_, A) => t2str A) conjuncts_with_pvs) ^ "\n") *)
                                                            val elaborated_conjuncts =
                                                                           List.map (fn (pv, Ak) =>
                                                                                        let in 
                                                                                            (pv, elaborateType (rctx, mctx) (mlify_constructor_type tvs Ak))
                                                                                        end)
                                                                                    conjuncts_with_pvs
                                                            val constructor =
                                                                       Constructor {c= pv,
                                                                                    nullary= nullary,
                                                                                    basetype= unquant_D,
                                                                                    contype= contype,
                                                                                    conjuncts= conjuncts_with_pvs,
                                                                                    elaborated_conjuncts= elaborated_conjuncts}
                                                            val _ = dprint (fn () => "is_my_con: CREATED CONSTRUCTOR")
                                                            val _ = dprint (fn () => P.p (fn pps => fn c => P.printConstructor pps false c) constructor ^ ".\n")
                                                        in
                                                            SOME constructor
                                                        end
                                                  | NONE => NONE
                            val bool = Option.isSome result
                            val _ = dprint (fn () => " = " ^ Bool.toString bool)
                          in
                              result
                          end
                  | is_my_con _ = NONE

                val new_relevant_cons =  List.mapPartial  is_my_con  locally_defined_cons
                val cons = constructors @ new_relevant_cons


                fun purge_subsets_sort sort = case sort of
                     X.Base _ => sort
                   | X.Product list => X.Product (List.map purge_subsets_sort list)
                   | X.List sort => X.List (purge_subsets_sort sort)
                   | X.Subset (sort, sym, constraint) =>
                        (* XXX *)  (* unsound! *)
                         purge_subsets_sort sort

                and purge_subsets_list list = List.map purge_subsets_sort list

                fun purge_subsets_fields list = case list of
                    [] => []
                  | (fieldname, (sort, default)) :: rest =>
                       (fieldname, (purge_subsets_sort sort, default)) :: (purge_subsets_fields rest)

                fun purge_subsets sorting = case sorting of
                     X.Sorting.None => X.Sorting.None
                   | X.Sorting.Nameless (sort, default) => X.Sorting.Nameless (purge_subsets_sort sort, default)
                   | X.Sorting.Fields list => X.Sorting.Fields (purge_subsets_fields list)

                val purged_sorting = purge_subsets sorting

                val elabTypedec = Datatype {tc= tc,
                                            builtin= builtin,
                                            params= params,
                                            sorting= X.Sorting.None, 
                                            constructors= cons}
                
                val typeinfo = Typeinfo{indexsort= purged_sorting,
                                        parameters= params,
                                        elabTypedecs= [elabTypedec]}

                val _ = dprint (fn () => "Context.addTypeinfo " ^ TC.toString tc)
                val rctx = Context.addTypeinfo (rctx, (tc, typeinfo))
(*                val _ = print ("After addTypeinfo, rctx is " ^ rctxToString rctx ^ "\n") *)
            in
              (typecheck_cons (rctx, mctx)
                             purged_sorting
                             (tc, params)
                             (List.map (fn Constructor{c, basetype, nullary, ...} =>
                                                 let val nonnullary = if nullary then NONE else SOME ()
                                                     val _ = dprint (fn () => "CONSTRUCTOR " ^ PV.toString c ^ ": " ^ (if (not nullary) then "non-nullary" else "nullary") ^ "\n")
                                                 in
                                                     (c, nonnullary)
                                                 end)
                                            cons)
                             cons
               ,
               elabTypedec)
            end
      
      | typecheck_typedec datacons (rctx, mctx) (Synonym {tc, tv, params, definition}) = 
            let val mctx = addExtype mctx tv
                val mctx = solveExtype "type synonym" mctx tv (fn UnknownEx => SolvedEx definition)
                val (mctx, definition) = Context.substExtypevarAuto mctx definition
            in
                ((rctx, mctx),
                 Synonym {tc= tc,
                                   tv= tv,
                                   params= params,
                                   definition= elaborateType (rctx, mctx) definition})
            end

    and typecheck_cons ctx sorting (tc, params) allcons cons = case cons of 
         [] => ctx
      | con::rest => typecheck_cons
                                 (typecheck_con ctx sorting (tc, params) allcons con)
                                 sorting
                                 (tc, params)
                                 allcons
                                 rest

   (* Signal *)
    and typecheck_con (rctx, mctx) sorting (tc, params) allcons (Constructor {c, basetype, contype, nullary, conjuncts, elaborated_conjuncts})  =
        (* Check that contype is:
even list 
          (1) a well-formed constructor signature type;
          (2) a refinement of basetype.
               *)
        let
            val unquant_basetype = basetype
            val basetype = Sdml.quantifyCtype unquant_basetype params
            val unquant_contype = contype
            val contype = Sdml.quantifyCtype unquant_contype params
        in
            case good unquant_basetype unquant_contype of
               SOME (nullary, texps) =>
                    (addConinfo rctx (c, Coninfo{basetype= basetype,
                                                                     contype= contype,
                                                                     conjuncts= conjuncts,
                                                                     unquant_basetype = unquant_basetype,
                                                                     unquant_contype = unquant_contype,
                                                                     tc= tc,
                                                                     allcons= allcons}),
                     mctx)
             | _ => 
                raise_AllDead mctx (fn () => "Constructor  " ^ PV.toShortString c
                                           ^ "  of base type  " ^ t2str basetype
                                           ^ "  annotated by  " ^ t2str contype)
        end



  fun letARainOfIniquityFallOnTheHeadsOfThoseWhoFailedToEstablishACleanAnnotationMechanismInSML () =
      let val _ = subtype : result failure -> int -> ctx -> Sdml.texp -> Sdml.texp -> (result failure * ctx * coercion -> result) -> result
          val _ = inferConapp :
                  result failure
              -> ctx
              -> Location.location
              -> PV.sym
              -> Sdml.texp
              -> (result failure * mctx * Sdml.pv(*conjunct*) * Sdml.texp * Sdml.texp (* * result *) -> result)
              -> result
      in
          ()
      end

    and inferConapp (failure : result failure) (rctx : rctx, mctx : mctx) loc c result (k : result failure * mctx * pv * Sdml.texp * Sdml.texp (* * result *) -> result) =
        let val _ = dprnt "inferConapp"
            val conjuncts = lookupConjuncts "check Conapp" rctx c
(*            val contype = Inject.clean contype *)
            val _ = dprint (fn () => "inferConapp " ^ PV.toShortString c ^ " : " ^ "...XXX..." (* t2str contype *))
            fun push failure (mctx, (ck, contype)) =
                let fun fail_disjunctive() = (dprnt "inferConapp: Exis / Conj / Union / Bot in constructor type?!";
                                              fail "inferConapp: disjunctive")
                    val contype = Inject.inject_type (lookupSorting rctx) contype
                in
                    case contype of
                        Arrow(dom, cod) =>
                                Subtype.subtype failure 0 (rctx, mctx) cod result
                                  (fn (failure, (_, mctx), constraint (*XXX*)) =>
                                      k (failure, mctx, ck, dom, cod))
                      | All(tv, uu, AA) =>
                            let val failure = fn _ =>
                                  let val extv = TV.new tv
                                      val mctx = addExtype mctx extv
                                      val A = Types.substTypevar [(tv, Extypevar extv)] AA
  (*                                    val _ = print ("push All INST " ^ t2str AA ^ " ====> " ^ t2str A ^ "\n") *)
                                  in
                                    push failure (mctx, (ck, A))
                                  end
                            in
                              try_hints failure (rctx, mctx) (uu, (*D.getHints (getG mctx)*)[]   (*ZZZHINTS*) )
                                (fn (failure, mctx, hintType) =>
                                   let val A = Types.substTypevar [(tv, hintType)] AA
                                       val _ = dprint (fn () => "[Conapp]....using hint = " ^ P.pTexp A)
                                   in
                                     push failure (mctx, (ck, A))
                                   end)
                            end

                      | Rsect(A1, A2) =>
                            let val (A1, A2) = perm (A1, A2)
                            in
                                push (fn _ => push failure (mctx, (ck, A2))) (mctx, (ck, A1))
                            end
                      
                      | Univ(aa, sort, AA) =>
                            let val a = IndexSym.new aa
                                val A = Types.substIndex [(aa, X.Evar a)] AA
                            in
                                push failure (forceSingleton (mctx %% Iexists(a, sort)), (ck, A))
                            end
                      | Implies(P, A) => 
                          && failure (mctx, P) (fn mctx => push failure (mctx, (ck, A)))
                      | Exis _ => fail_disjunctive()
                      | Conj _ => fail_disjunctive()
                      | Union _ => fail_disjunctive()
                      | Runion _ => fail_disjunctive()
                      | Bot => fail_disjunctive()
                      | A => fail ("inferCon: constructor type " ^ t2str A ^ " is not a refinement intersection of arrows (that is, (A1 -> t1) && ... && (An -> tn))")
                end

            fun pushConjunct failure (mctx, conjuncts) = case conjuncts of
               [] => raiseDead failure mctx loc (fn () => "inferConapp.pushConjunct.[]")
             | (ck, A1) :: rest =>
                   let (* val (A1, A2) = perm (A1, A2) *)
                   in
                       push (fn _ => pushConjunct failure (mctx, rest))
                            (mctx, (ck, A1))
                   end
        in
            pushConjunct failure (mctx, conjuncts)
        end



    and inferNullaryCon (failure : result failure) (rctx : rctx, mctx : mctx) loc c (k : result failure * mctx * (Sdml.texp * locexp) -> result) =
        let val _ = dprnt "inferNullaryCon"
            val conjuncts = lookupConjuncts "inferNullaryCon" rctx c
(*            val contype = Inject.clean contype *)
            val _ = dprint (fn () => "inferNullaryCon " ^ PV.toShortString c ^ " : " ^ "...XXX..." (* t2str contype *))
            
            fun elabConjuncts conjuncts = case conjuncts of
               [(ck, _)] => (loc, Con ck)
             | (ck, _) :: rest =>
                   let in
                      (loc, Tuple [(loc, Con ck),
                              elabConjuncts rest])
                   end

            fun buildIntersection conjuncts = case conjuncts of
              [(ck, last)] => last
            | (ck, Ak) :: rest => 
                   Rsect (Ak, buildIntersection rest)
        in
            k (failure, mctx, (buildIntersection conjuncts, elabConjuncts conjuncts))
        end



    fun fold failure (_, mctx) k f [] = k (failure, mctx)
      | fold failure (rctx, mctx) k f (x::xs) = f (failure, mctx) x (fn (failure, mctx) => fold failure (rctx, mctx) k f xs)
    
    fun fold_elab failure (_, mctx) k f [] acc =
             k (failure, mctx, acc)
      | fold_elab failure (rctx, mctx) k f (x::xs) acc =
             f (failure, mctx) x (fn (failure, mctx, elab) => fold_elab failure (rctx, mctx) k f xs (acc @ [elab]))

    fun fold_elab' failure ctx k f xs = fold_elab failure ctx k f xs []
    val fold_elab = (fold_elab' : result failure
                                              -> ctx
                                              -> (result failure * mctx * locexp list -> result)
                                              -> (result failure * mctx -> 'a -> (result failure * mctx * locexp -> result) -> result)
                                              -> 'a list
                                            -> result)

    fun freshenIndexVar (aa, sort) (TUP {rctx= rctx,
                                         conjunct= conjunct,
                                         things= (exvars, assns''),
                                         varmap= varmap,
                                         constraint= W'',
                                         domain= dom'',
                                         codomain= cod''}) =
        let val a = IndexSym.new aa
            val substitution = [(aa, X.Uvar a)]
            val W'' = X.Constraint.subst substitution W''
            val dom'' = Option.map (Types.substIndex substitution) dom''
            val cod'' = Types.substIndex substitution cod''
        in
            TUP {rctx= rctx,
                 conjunct= conjunct,
                 things= (exvars, Iall (a, sort) :: assns''),
                 constraint= W'',
                 varmap= Renaming.extend (a, aa) varmap,
                 domain= dom'',
                 codomain= cod''}
        end
        
    fun freshen (rctx, conjunct, trackinfos, W'', dom'', cod'') =
        foldr(* MUST be right fold, or order of assumptions will be reversed! *)
             (fn (IALL(aa, sort),  tup) => 
                     freshenIndexVar (aa, sort) tup
                
               | (ITYPEVAR aa,  TUP {rctx= rctx, conjunct= conjunct, things= (exvars, assns''),
                                     varmap,
                                     constraint= W'',
                                     domain= dom'',
                                     codomain= cod''}) =>
(*                         let val a = TV.new aa
                     val substitution = [(aa, Typevar a)]
                     val W'' = W'' (* W'' is a constraint, and therefore does not contain typevars *)
                     val dom'' = Option.map (Types.substTypevar substitution) dom''
                     val cod'' = Types.substTypevar substitution cod''
                 in
                    TUP {rctx= rctx,
                         conjunct= conjunct,
                         things= assns'' +--+ a,
                         constraint= W'',
                         varmap= varmap,
                         domain= dom'',
                         codomain= cod''}
                 end
*)
                         let val a = TV.new aa
                             val substitution = [(aa, Extypevar a)]
                             val W'' = W'' (* W'' is a constraint, and therefore does not contain typevars *)
                             val dom'' = Option.map (Types.substTypevar substitution) dom''
                             val oldCod'' = cod''
                             val cod'' = Types.substTypevar substitution cod''
                             val _ = dprint (fn () => "freshen INST " ^ t2str oldCod'' ^ " ====> " ^ t2str cod'')
                         in
                             TUP {rctx= rctx,
                                  conjunct= conjunct,
                                  things= (a :: exvars, assns''),
                                  varmap= varmap,
                                  constraint= W'',
                                  domain= dom'',
                                  codomain= cod''}
                         end)
              (TUP {rctx= rctx,
                    conjunct= conjunct,
                    things= ([], []), 
                    constraint= W'',
                    varmap= Renaming.empty,
                    domain= dom'',
                    codomain= cod''})
              trackinfos

    fun freshen_tyvars (rctx, conjunct, trackinfos, W'', dom'', cod'') =
        foldr(* MUST be right fold, or order of assumptions will be reversed! *)
             (fn (IALL(aa, sort),  TUP {rctx= rctx, conjunct= conjunct, things= (exvars, assns''),
                                        varmap,
                                        constraint= W'',
                                        domain= dom'',
                                        codomain= cod''}) =>
                     let val W'' = W''
                         val dom'' = dom''
                         val cod'' = cod''
                     in
                         TUP {rctx= rctx,
                              conjunct= conjunct,
                              things= (exvars, Iall (aa, sort) :: assns''),
                              constraint= W'',
                              varmap= varmap,
                              domain= dom'',
                              codomain= cod''}
                     end
               | (ITYPEVAR aa,  TUP {rctx= rctx, conjunct= conjunct, things= (exvars, assns''),
                                     varmap,
                                     constraint= W'', domain= dom'', codomain= cod''}) =>
(*                         let val a = TV.new aa
                     val substitution = [(aa, Typevar a)]
                     val W'' = W'' (* W'' is a constraint, and therefore does not contain typevars *)
                     val dom'' = Option.map (Types.substTypevar substitution) dom''
                     val cod'' = Types.substTypevar substitution cod''
                 in
                    TUP {rctx= rctx,
                         conjunct= conjunct,
                         things= assns'' +--+ a,
                         constraint= W'',
                         varmap= varmap,
                         domain= dom'',
                         codomain= cod''}
                 end
*)
                         let val a = TV.new aa
                             val substitution = [(aa, Extypevar a)]
                             val W'' = W'' (* W'' is a constraint, and therefore does not contain typevars *)
                             val dom'' = Option.map (Types.substTypevar substitution) dom''
                             val oldCod'' = cod''
                             val cod'' = Types.substTypevar substitution cod''
                             val _ = dprint (fn () => "freshen INST " ^ t2str oldCod'' ^ " ====> " ^ t2str cod'')
                         in
                             TUP {rctx= rctx,
                                  conjunct= conjunct,
                                  things= (a :: exvars, assns''),
                                  constraint= W'',
                                  varmap= varmap,
                                  domain= dom'',
                                  codomain= cod''}
                         end)
              (TUP {rctx= rctx,
                    conjunct= conjunct,
                    things= ([], []), 
                    constraint= W'',
                    varmap= Renaming.empty,
                    domain= dom'',
                    codomain= cod''})
              trackinfos

  fun letARainOfIniquityFallOnTheHeadsOfThoseWhoFailedToEstablishACleanAnnotationMechanismInSML () =
      let val _ = infer : result failure
                       -> inference_disposition
                       -> ctx
                       -> (Sdml.locexp * pexp)
                       -> (result failure * mctx * (Sdml.texp * result) -> result)
                       -> result

          val _ = check : result failure -> ctx -> (Sdml.locexp * pexp) -> Sdml.texp -> (result failure * mctx * result -> result) -> result
          val _ = check' : result failure -> ctx -> (Sdml.locexp * pexp) -> Sdml.texp -> (result failure * mctx * result -> result) -> result

          val _ = check_annotation : result failure -> ctx -> Location.location -> Sdml.annotation
                              -> (result failure * mctx * Sdml.texp -> result)
                              -> result

          val _ = check_arms : result failure -> ctx -> Sdml.texp -> ((Sdml.arm * parm) list * Sdml.arm list)
                            -> Sdml.pattern (* list *)
                            -> Sdml.texp
                            -> Location.location
                            -> (result failure * mctx * Sdml.arm list -> result)
                            -> result
                               
          val _ = infer_decs : result failure -> ctx -> Location.location -> (Sdml.locdec * pdec) list -> (result failure * ctx * Sdml.locdec list -> result) -> result
      in
          ()
      end
       
    and infer failure disposition ctx ((loc, e), (path, pe)) (k : result failure * mctx * (texp * result) -> result) =
(*        case memoInfer (disposition, ctx) (!path) of
            NONE =>
*)
                inferNoMemo failure disposition ctx ((loc, e), (path, pe)) k
(*
          | _ => raise Match
*)

    and inferNoMemo (failure : result failure)
                    disposition (rctx : rctx, mctx : mctx)
                    ((loc_e as (loc, e)),  (path, pe))
                    (k : result failure * mctx * (texp * result) -> result) =
        let val k =
                fn (failure, mctx, (tA, elab)) => 
                   let val _ = dprint (fn () => "infer:: " ^ t2str tA ^ " for expression at " ^ Location.toString loc)
                   in
                       k (failure, mctx, (tA, elab))
                   end

            fun genProj mctx A n (loc, e) =
                let val annotation = (* [([], A)] *)
                                     [AnnotationType.Type A]
                in
                    finalSubstLocexp mctx (loc, redalert_Proj(Int.toString n, (loc, Anno((loc, e), annotation))))
                end

            fun push (failure : result failure) (mctx, (tA, elab : locexp)) =
                let val tA = Inject.inject_type (lookupSorting rctx) tA
                in
                    case disposition of
                        WANT_ORDINARY_TYPE =>
                            let in case tA of
                                Sect(A1, A2) =>
                                    let val (A1, A2) = perm (A1, A2)
                                        val elabType = elaborateType (rctx, mctx) (Product [A1, A2])
                                    in
                                        dprint (fn () => "### PUSHING &-left: " ^ t2str A1);
                                        push (fn _ =>
                                                   let in dprint (fn () => "### PUSHING &-right: " ^ t2str A2);
                                                          push failure (mctx, (A2, genProj mctx elabType 2 elab)) end)
                                             (mctx, (A1, genProj mctx elabType 1 elab))
                                    end
                               | Rsect (A1, A2) =>
                                    let val (A1, A2) = perm (A1, A2)
                                    in
                                        dprint (fn () => "### PUSHING &&-left: " ^ t2str A1);
                                        push (fn _ =>
                                                   let in dprint (fn () => "### PUSHING &&-right: " ^ t2str A2);
                                                          push failure (mctx, (A2, elab)) end)
                                             (mctx, (A1, elab))
                                    end
                              | All(tv, uu, AA) =>
                                    let val failure = fn _ =>
                                        let val extv = TV.new tv
                                            val mctx = addExtype mctx extv
                                            val A = Types.substTypevar [(tv, Extypevar extv)] AA
                                            val _ = dprint (fn () => "push''INST " ^ t2str AA ^ " ====> " ^ t2str A)
                                        in
                                            push failure (mctx, (A, elab))
                                        end
                                    in
                                        try_hints failure (rctx, mctx) (uu, (*D.getHints (getG mctx)*)[] (*ZZZHINTS*))
                                          (fn (failure, mctx, hintType) =>
                                           let val A = Types.substTypevar [(tv, hintType)] AA
                                               val _ = dprint (fn () => "[Elim].............proceeding with  " ^ P.pTexp A)
                                           in
                                               push failure (mctx, (A, elab))
                                           end)
                                    end
                              | Univ(aa, sort, AA) =>
                                    let
                                        val a = IndexSym.new aa
                                        val A = Types.substIndex [(aa, X.Evar a)] AA
                                                
                                        val _ = dprint (fn () => "push Univ: Iexists " ^ Indexing.Sort.toString sort)
                                    in
                                        push failure (forceSingleton (mctx %% Iexists(a, sort)),
                                                      (A, elab))
                                    end
                              | Implies(P, A0) => && (failure) (mctx, P) (fn mctx => push failure (mctx, (A0, elab)))
                              | Conj(P, A0) => 
                                    push failure (forceSingleton (mctx %% Prop P), (A0, elab))
        (* YYY OK
                              | Conj(P, A0) => 
                                     push failure (mctx, A0)
        *)


                              | _ => let val _ = dprint (fn () => "infer: pushing " ^ t2str tA ^ " for expression at " ^ Location.toString loc)
                                     in
                                         k (failure, mctx, (tA, elab))
                                     end
                            end
                      | MAINTAIN_PRINCIPALITY =>   (* Don't need to expose an ordinary type,
                                                    so don't introduce wasteful and possibly counterproductive
                                                    branching *)
                            let in case tA of
                                Conj(P, A0) =>
                                    push failure (forceSingleton (mctx %% Prop P), (A0, elab))
        (* YYY OK
                                Conj(P, A0) => push failure (mctx, A0)
        *)
                              | All(tv, uu, AA) =>
                                    let val tryElim = fn _ =>
                                        let val extv = TV.new tv
                                            val mctx = addExtype mctx extv
                                            val A = Types.substTypevar [(tv, Extypevar extv)] AA
                                            val _ = dprint (fn () => "pushMP-INST " ^ t2str AA ^ " ====> " ^ t2str A)
                                        in
                                            push failure (mctx, (A, elab))
                                        end
                                        val tryWholeType = fn _ => k (tryElim, mctx, (tA, elab))
                                    in
                                        try_hints tryWholeType (rctx, mctx) (uu, (*D.getHints (getG mctx)*)[] (*ZZZHINTS*))
                                          (fn (failure, mctx, hintType) =>
                                           let val A = Types.substTypevar [(tv, hintType)] AA
                                               val _ = dprint (fn () => "[Elim'] INST " ^ t2str AA ^ " ====> " ^ t2str A)
                                               val _ = dprint (fn () => "[Elim'] proceeding with  " ^ P.pTexp A)
                                           in
                                               push failure (mctx, (A, elab))
                                           end)
                                    end
                              | _ =>
                                    k (failure, mctx, (tA, elab))
                            end
                end

(**********************
            (let val _ = dprnt ("infer: pushing " ^ t2str tA ^ " for expression at " ^ Location.toString loc)
             in k (ctx, tA) end) handle Dead stuff =>
                 let in case disposition of
                     WANT_ORDINARY_TYPE =>
                         let in case tA of
                             Sect(tA1, tA2) => ((dprnt ("### PUSHING &-left: " ^ t2str tA1); push (ctx, tA1))
                                                handle Dead _ =>
                                                    (dprnt ("### PUSHING &-right: " ^ t2str tA2); push (ctx, tA2)))
                           | Univ(aa, sort, AA) => let val a = IndexSym.new aa
                                                       val A = Types.substIndex [(aa, X.Evar a)] AA
                                                   in
                                                       push (ctx %% Iexists(a, sort),
                                                             A)
                                                   end
                           | Implies(P, A0) => push ((noUnks "infer Implies" ctx P; &&(ctx, P)), A0)
                           | Conj(P, A0) => 
                                 push (ctx %% (Prop P), A0)
(* YYY XXX
                             | Conj(P, A0) => push(ctx, A0)
*)
                           | _ => raise Dead stuff
                         end
                   | MAINTAIN_PRINCIPALITY =>   (* Caller doesn't need to try to expose an ordinary type,
                                                 so don't introduce wasteful and possibly counterproductive
                                                 branching *)
                         failure stuff
                 end
***************)
        in
            case (e, pe) of
                (Var pv, Path.Var) =>  (* print ("inferring for " ^ PV.toShortString pv ^"\n"); *)
                    let val (pv_texp, _) = lookupOrd "infer Var" mctx pv
                    in
                        push failure (mctx, (pv_texp,  (*elab=*) loc_e))
                    end

              | (Con c, Path.Con) =>
                      (* push failure (mctx, (lookupContype (*XXX*) "infer Con" rctx c,  (*elab=*) loc_e)) *)
                      inferNullaryCon failure (rctx, mctx) loc c k
              
              | (Spy (stuff, e0), Path.Spy (pe0)) =>
                    infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (e0, pe0)
                          (fn (failure, mctx, (A0, elab0)) =>
                              (print ("Spy: " ^ P.pExp (#2 e0));
                               print (" synthesizes " ^ t2str A0 ^ " =====> " ^ t2str' mctx A0 ^ "\n");
                               print (" context is " ^ mctxToString mctx ^ "\n");
                               k (failure, mctx, (A0, (*elab=*) elab0)))
                          )
              | (Const(texp, _),  Path.Const) => push failure (mctx, (texp, (*elab=*) loc_e))

              | (Tuple [],  Path.Tuple []) => push failure (mctx, (Product[], (*elab= *) loc_e))

              | (Tuple exps,  Path.Tuple pexps) =>
                   let fun aux failure mctx (accTypes, accElabs) pairs = case pairs of
                            [] =>
                                 push failure (mctx, (Product (List.rev accTypes), (loc, Tuple (List.rev accElabs))))
                          | (exp, pexp) :: rest => 
                                 infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (exp, pexp)
                                    (fn (failure, mctx, (A0, elab0)) =>
                                        aux failure mctx
                                            (A0 :: accTypes,  elab0 :: accElabs)
                                            rest)
                   in
                       aux failure mctx ([], []) (ListPair.zip (exps, pexps))
                   end
              
              | (RecordExp (fld, fldExp), Path.RecordExp pexp) =>
                    infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (fldExp, pexp)
                             (fn (failure, mctx, (A, elab)) =>
                                 k (failure, mctx, (Record(fld, A),  (* loc,  RecordExp*) ( (*fld1,*) elab))))
               
              | (Let (decs, locexp),  Path.Let(pdecs, pexp)) =>
                (* XXX should add `frame' here for properly hygienic contexts *)
                    infer_decs failure (rctx, mctx) loc (ListPair.zip (decs, pdecs))
                      (fn (failure, (rctx', mctx'), elab_decs) =>
                         infer failure MAINTAIN_PRINCIPALITY (rctx' (*rctx?*), mctx') (locexp, pexp)
                              (inferrefract k (fn elab_body => (loc, Let (elab_decs, elab_body)))))

              | (LET(X, locexp1, exp2), Path.LET(pexp1, pexp2)) =>
                    infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (locexp1, pexp1)
                          (fn (failure, mctx, (tA, elab1)) =>
                              Context.frame mctx
                                            (fn mctx =>
                                                let val (mctx, tA) = substExtypevarAuto mctx tA
                                                in
                                                    infer failure disposition (rctx, mctx +- (X, (tA, NONE))) ((loc, exp2), pexp2)
                                                end)
                                            (inferrefract k (fn elab_body => (loc, Let([(loc, Dec(X, ValKW, elab1))], elab_body)))))

              | (LETSLACK(X, locexp1, exp2), Path.LETSLACK(pexp1, pexp2)) =>  (* XXX *)
                    infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (locexp1, pexp1)
                          (fn (failure, mctx, (tA, elab1)) =>
                              Context.frame mctx
(*
                                            (fn mctx =>
                                                let val (mctx, tA) = substExtypevarAuto mctx tA
                                                in
                                                    infer failure disposition (rctx, mctx +- (X, (tA, NONE))) ((loc, exp2), pexp2)
                                                end)
*)
                                            (fn mctx =>
                                                infer failure disposition (rctx, mctx +- (X, (substExtypevarNoAuto mctx tA, NONE))) ((loc, exp2), pexp2))

                                            (inferrefract k (fn elab_body => (loc, Let([(loc, Dec(X, ValKW, elab1))], elab_body)))))
              
              | (Merge exps, Path.Merge pexps) =>
                   let fun try failure mctx [exp] k = 
                                  infer failure disposition (rctx, mctx) exp k
                            | try failure mctx (exp :: exps) k =
                                  let
                                      val ((_, e), _) = exp
                                      val _ = dprint (fn () => "infer Merge: " ^ P.pExp e)
                                  in
                                       infer
                                          (fn _ => try failure mctx exps k)
                                          disposition
                                          (rctx, mctx)
                                          exp
                                          (fn (failure1, mctx, (A1, elab1)) =>
                                                   try failure1 mctx exps (fn (failure2, mctx, (A2, elab2)) =>
                                                                                 k (failure2,
                                                                                    mctx,
                                                                                    (Sect(A1, A2),  (loc, Tuple[elab1, elab2]))
                                                                                    )
                                                                                )
                                          )
                                  end
                   in
                     try failure mctx (ListPair.zip (exps, pexps)) (fn (failure, mctx, (A, elab)) => push failure (mctx, (A, elab)))
                   end


              | (App (e1, e2),  Path.App (pe1, pe2)) =>
                    infer failure WANT_ORDINARY_TYPE (rctx, mctx) (e1, pe1) (fn (failure, mctx, (t1, elabFun)) =>
                                  case t1 of Arrow(A,B) =>
                                             ( (* print "Attention!\n";
                                              print (t2str t1 ^  "\n");
                                              print ("CTX= " ^ ctxToString (rctx, mctx) ^  "\n"); *)
                                      (check failure (rctx, mctx) (e2, pe2) A (fn (failure, mctx, elabArg) =>
                                       let val _ = dprint (fn () => "App elabFun =  " ^ P.pLocexp elabFun)
                                           val _ = dprint (fn () => "App elabArg =  " ^ P.pLocexp elabArg)
                                       in
                                           push failure (mctx, (B, (loc, App(elabFun, elabArg))))
                                       end)))
                                | _ => raiseDead failure mctx loc (fn () => "infer App")
                         )


              | (Fn (x,body), Path.Fn (pbody)) =>
                     let val exalpha1 = TV.fresh "synthAbs1"
                         val exalpha2 = TV.fresh "synthAbs2"

                         val mctx = addExtype mctx exalpha1
                         val mctx = addExtype mctx exalpha2

                         val arrow = Arrow (Extypevar exalpha1, Extypevar exalpha2)
                     in
                         check' failure (rctx, mctx) (loc_e, (path, pe)) arrow
                                (fn (failure, mctx, elab) =>
                                    k (failure, mctx, (arrow, elab)))
                     end


              | (Anno(e1 as (loc1,exp1), anno), Path.Anno(pe1)) =>
                    let (* val _ = PRINT "Anno\n"
                        val _ = message (fn () => pExp exp1)
                        val _ = PRINT ("    <<<< " ^ P.pAnnotation anno ^ "\n") *)
                    in
                        check_annotation failure (rctx, mctx) loc1 anno
                                      (fn (failure, mctx, texp) =>
                                          check failure (rctx, mctx) (e1, pe1) texp
                                                     (fn (failure, mctx, elab) =>
                                                         push failure (mctx, (texp, elab))))
                    end

              | (Leftanno(leftanno, e1 as (loc1,exp1)), Path.Leftanno(pe1)) =>
                    let 
                        val (pv, B) = case leftanno of
                                         LeftProgramVar (x, B) => (x, B)
                    in
                        case lookupOrd "ctxsubtype" mctx pv of
                                 (pv_texp, _) =>
                                     subtype failure 0 (rctx, mctx) pv_texp B
                                             (fn (failure, (_(*XXX*), mctx), coercion(*XXX*)) =>
                                                 infer failure disposition (rctx, mctx) (e1, pe1) k)
                    end

              | (Proj(fld, e0), Path.Proj(pe0)) =>
                   let in case Int.fromString fld of
                              NONE =>    (* record projection *)
                                 infer failure WANT_ORDINARY_TYPE (rctx, mctx) (e0, pe0) (fn (failure, mctx, (t0, elab0)) =>
                                                 case t0 of Record (fld0, A0) =>
                                                     if fld <> fld0 then
                                                         raiseDead failure mctx loc (fn () => "infer Proj [record, field mismatch]")
                                                     else
                                                         k (failure, mctx, (A0, ((* loc, Proj *) ( (* fld0,*) elab0))))
                                                                          (* elaborate records to their single component,
                                                              to avoid SML's flex-record limitations *)
                                                          | _ => raiseDead failure mctx loc (fn () => "infer Proj [record, not record]")
                                  )
                            
                            | SOME n =>    (* tuple projection *)
                                 infer failure WANT_ORDINARY_TYPE (rctx, mctx) (e0, pe0) (fn (failure, mctx, (t0, elab)) =>
                                                 case t0 of Product ts =>
                                                     let val B = fn k => ((k (List.nth(ts, n - 1 (*List.nth is 0-based*) )))
                                                                     handle Subscript =>
                                                                                     raiseDead failure mctx loc (fn () => "Proj misapplied: "
                                                                                                                                               ^ Int.toString n ^ " in a "
                                                                                                                                               ^ Int.toString (List.length ts)
                                                                                                                                               ^ "-tuple")
                                                                          | exn => raise exn)
                                                         val annotation = (* [([], elaborateType (rctx, mctx) (Product ts))] *)
                                                                          [AnnotationType.Type (elaborateType (rctx, mctx) (Product ts))]
                                                         val projElab = (loc, redalert_Proj (Int.toString n, (loc, Anno(elab, annotation))))
                                                         val projElab = finalSubstLocexp mctx projElab   (* XXX --- too early? *)
                                                     in
                                                         B (fn B => push failure (mctx, (B, projElab)))
                                                     end
                                               | _ => raiseDead failure mctx loc (fn () => "infer Proj"))
                   end

              | (Lvar X, Path.Lvar) => 
                    let 
                        val doit =
                            let 
                                val (texpX, _(*locexp*)) = (lookupLinear "infer Lvar" mctx X)
                            in
                                fn () => push failure (mctx, (texpX, (loc, Var X)))
                            end
                            handle
                                exn as Context.LookupFailure stuff => 
                                       if varInSlack mctx X then
                                           fn () => raiseDead failure mctx loc (fn () => "Lvar-slack")
                                           (* fail ("linear/slack confusion: " ^ PV.toString X) *)
                                       else
                                           let in
                                               fail ("linear variable " ^ PV.toString X ^ " not in context (neither linear nor slack)")
                                               (* raise exn *)
                                           end
                    in
                        doit()
                    end
              
              | (Raise e0, Path.Raise pe0) =>
                    check failure (rctx, mctx) (e0, pe0) (Tycon(#exnTC (Context.getDistinguished rctx), X.N, [])) 
                          (fn (failure, mctx, elab) =>
                              push failure (mctx, (Bot, (loc, Raise elab))))
              
              | _ => raiseDead failure mctx loc (fn () => "infer1")
        end

(*****
    and caseCon (rctx, mctx) loc c result =
        let val contype = lookupCon "caseCon" rctx c
            val _ = dprint (fn () => "$*caseCon: ctx " ^ Location.toString loc ^ " " ^ PV.toShortString c ^ " (result= " ^ t2str result ^ ")")

            fun simul mctx contype B_right =
                case contype of
                    Arrow(dom, cod) =>
                      [(mctx, SOME dom, cod, B_right)]
                  | Sect(A1, A2) =>
                    (simul mctx A1 B_right) @ (simul mctx A2 B_right)
                  | Implies(P, A) =>
                    let val mctxOpt = let in SOME (&&&(mctx, P)) end handle Dead _ => NONE
                    in 
                        case mctxOpt of
                            NONE => []
                          | SOME mctx => simul mctx A B_right
                    end
                  | Univ(aa, sort, AA) =>
                      let val a = IndexSym.new aa
                          val A = Types.substIndex [(aa, X.Uvar a)] AA
                          val _ = dprint (fn () => "caseCon introducing " ^ IndexSym.toString a ^ " as a universal variable")
                      in
                          simul (mctx %% Iall(a, sort)) A B_right
                      end
                  | (Exis _ | Conj _ | Union _ | Bot) => (fail "caseCon: Exis / Conj / Union / Bot in constructor type?!")
                  | contype => (* this had better be a nullary constructor! *)
                        [(mctx, NONE, contype, B_right)]
        in
            simul mctx contype result
        end
*****)

    and caseCon_ACTUAL rctx loc (c, ctype) pat0 B =
        let val _ = dprint (fn () => "$*caseCon: ctx " ^ Location.toString loc ^ " " ^ PV.toShortString c)
            val failmessage = "caseCon_ACTUAL: Exis / Conj / Union / Bot in constructor type?!"

            fun refute (A, B) = case (A, B) of
                (Tycon (tcA, _, _),  Tycon (tcB, _, _)) =>
                    if tcA = tcB then
                        false
                    else if DS.blitheSubsort (tcA, tcB) then
                        false
                    else
                         (refutations := !refutations + 1; true) (* refuted! *)
              | (_, _) => false

            fun refute_pat (A, NONE) = false
              | refute_pat (A, SOME p) =
                    let in case (A, p) of
                        (_, WildPattern) => false
                      | (_, VarPattern _) => false
                      | (_, AsPattern (_, p)) => refute_pat (A, SOME p)
                      | (Product [], TuplePattern []) => false
                      | (Product (A1::As),  TuplePattern (p1::ps)) =>
                            let in 
                                refute_pat (A1, SOME p1)
                                orelse
                                refute_pat (Product As, SOME (TuplePattern ps))
                            end
                      | (A, CtorPattern (c, p0)) => 
                            let val ctype = Context.getConjunctType rctx c
                                val result = refute_push (c, ctype) p0 A
                            in
                                result
                                before
                                (if result then refutations := !refutations + 1 else ())
                            end
      (*                | (_, TuplePattern ps) => true    dangerous w/ extypevars *)
                      | (_, _) => false
                    end

            and refute_push (conjunct, contype) pat0 B =
                let val contype = Inject.inject_type (lookupSorting rctx) contype
                in
                    case contype of
                        Arrow(dom, cod) =>
                            refute (cod, B) orelse refute_pat (dom, pat0)
                      | Sect _ => false
                      | Rsect _ => false
                      | Implies(P, A) =>
                            refute_push (conjunct, A) pat0 B
                      | All(aa, uu, AA) =>
                            refute_push (conjunct, AA) pat0 B
                      | Univ(aa, sort, AA) =>
                            refute_push (conjunct, AA) pat0 B
                      | Exis _ => false
                      | Conj _ => false
                      | Union _ => false
                      | Runion _ => false
                      | Bot => false
                      | contype => (* this had better be a nullary constructor! *)
                            refute (contype, B)
                end


            fun push things prop (conjunct, contype) =
                let val contype = Inject.inject_type (lookupSorting rctx) contype
                in
                    case contype of
                        Arrow(dom, cod) =>
                            let (* fun accumulate rctx conArg givenArg =
                                  rctx
                             fun accumulateTyvarEquations rctx conArgs givenArgs = case (conArgs, givenArgs) of
                                       ([], []) => rctx
                                     | (conArg::conArgs, givenArg::givenArgs) =>
                                          accumulateTyvarEquations (accumulate rctx conArg givenArg) conArgs givenArgs
                           *)
                            in (* case (cod, B) of
                              (Tycon(_, _, conArgs), Tycon(_, _, givenArgs)) => *)
                               if refute (cod, B) orelse refute_pat (dom, pat0) then
                                   []
                               else
                                 [freshen ((* accumulateTyvarEquations *)rctx (*conArgs givenArgs*),
                                           conjunct,
                                           things,
                                           prop,
                                           SOME dom,
                                           cod)]
                            end
                      | Sect (A1, A2) =>
                            (print ("caseCon_ACTUAL: Error: individual conjunct "
                                    ^ PV.toString conjunct ^ " is an intersection: "
                                    ^ t2str contype ^ "\n");
                             raise Option)

                      | Rsect (A1, A2) =>
                            (push things prop (conjunct, A1)) @ (push things prop (conjunct, A2))
                      
                      | Implies(P, A) =>
                            push things (X.mkAND(prop, P)) (conjunct, A)
                      | All(aa, uu, AA) =>
                            let (* val a = TV.new aa
                                val A = Types.substTypevar [(aa, Typevar a)] AA
                                val _ = dprint (fn () => "caseCon introducing " ^ tv2str a ^ " as a [universal] type variable") *)
                                 val _ = dprint (fn () => "caseCon NOTINST " ^ t2str AA ^ " ====> " ^ "...")
                            in
                                push (ITYPEVAR(aa) :: things) prop (conjunct, AA)   (* XXX *)
                            end
                      | Univ(aa, sort, AA) =>
                            let (* val a = IndexSym.new aa
                                val A = Types.substIndex [(aa, X.Uvar a)] AA
                                val _ = dprint (fn () => "caseCon introducing " ^ IndexSym.toString a ^ " as a universal variable") *)
                            in
                                push (IALL(aa, sort) :: things) prop (conjunct, AA)   (* XXX *)
                            end

                      | Exis _ => fail failmessage
                      | Conj _ => fail failmessage
                      | Union _ => fail failmessage
                      | Bot => fail failmessage
                      | contype => (* this had better be a nullary constructor! *)
                            [freshen (rctx, conjunct, things, prop, NONE, contype)]
                end

        in
            push [] X.TRUE (c, ctype)
        end
  
    and caseCon rctx loc (c, ctype) pat B =
        let val caseCon = caseCon_ACTUAL
                          :
                          rctx
                       -> Location.location
                       -> (pv * texp)  (* (conjunct, conjunct type) *)
                       -> pattern option
                       -> texp
                       -> tuple list (* (rctx * trackinfo * X.constraint * texp option(*domain*) * texp(*codomain*)) list *)
        in
            caseCon rctx loc (c, ctype) pat B
        end

    and freeLvars e =
        let val freevars : pv list ref = ref []
            val foldspec = SdmlFold.expSpec
                  (fn e => (case e of Lvar X => freevars := X :: (!freevars) | _ => (); e))
            val _ = SdmlFold.fold_exp foldspec e
        in
            !freevars
        end
    
    and zorch (loc, e) linear =
        let val freevars = freeLvars e
            fun strip Empty = Empty
              | strip (Ctx(X, texp, rest)) = if MyList.contains X freevars then Ctx(X, texp, strip rest)
                                             else strip rest
        in
            strip linear
        end

    and check failure (ctx as (rctx, mctx)) ((loc, e), (path, pe)) C k =
(*        case !r_memoize of
            NoMemo =>
*)
                    checkNoMemo failure ctx ((loc, e), (path, pe)) (Inject.inject_type (lookupSorting rctx) C) k
(*
                              | _ => 
                            let val t = applyEx mctx t
                            in case memoCheck (ctx, t) (!path) of
                                NONE =>
                                    let val ctxes = ref []
                                    in
                                       (checkNoMemo
                                         (fn stuff =>
                                             (Counter.INC "memoAdd" memoAdd;
                                              path := MCheck((ctx, t), (*(List.rev o List.rev)*) (!ctxes)) :: (!path);
                                              failure stuff))
                                        ctx ((loc, e), (path, pe)) t
                                        (fn (failure, mctx') =>
                                         let val ctx' = (rctx, mctx')
                                         in 
                                             ctxes := ctx' :: (!ctxes);
                                             k (failure, mctx')
                                         end))
                                    end
                              | SOME (ctxes, info) =>
                                    (Counter.INC "memoHit" memoHit;
                    (*                 pprint ((fn () => "@@@memoHit @ " ^ Location.toString loc ^ "\n"));
                                     pprint ((fn () => "@@@    " ^ ctxToString ctx ^ "\n")); *)
                                     let fun runThrough failure [] = raiseDead failure mctx loc (fn () => "memoized failure")
                                           | runThrough failure ((ctxM as (_, mctxM)) :: ctxes) =
                                             let (*val _ = print ("Context stored in memo: " ^ ctxToString ctxM ^ "\n") *)
                                                 fun partition [] = ([], [])
                                                   | partition (infon :: rest) =
                                                       let val (left, right) = partition rest
                                                       in
                                                           case infon of
                                                               InfoIndexSym stuff => (stuff :: left, right)
                                                             | InfoBarrierID stuff => (left, stuff :: right)
                                                       end
                                                 val (newVarmap, barrierIDMap)  = partition info
                                                 val mctxM2 = mapBarrierIDs mctxM barrierIDMap
                                                 val mctxM3 = compVarmap mctxM2 (Renaming.fromList newVarmap)
                                             in
                                                 k (fn _ => runThrough failure ctxes,
                                                    mctxM3)
                                             end
                                     in
                                         runThrough failure ctxes
                                     end)
                            end
*)

    (* checkNoMemo:

       Splits on disjuncts in state.
       If no disjuncts, just calls checkNoMemoCORE.
    *)
    and checkNoMemo failure (rctx, mctx) (e as (loc,exp), ppe as (path, pe)) t (k : result failure * mctx * result -> result) =
        let val state = getState mctx
            fun continue failure (rctx, mctx) k =
                checkNoMemoCORE failure (rctx, mctx) (e, ppe) t k
        in
            case state of
                NONE =>
                    continue failure (rctx, mctx) k

       (* Case-splitting on disjuncts *)
              | SOME (state, djs) =>
                    let val _ = case djs of [] => () | _ => print ("HERE WE GO\n")
                        fun zapDjs mctx = mapUpdateState mctx (fn (state, djs) => SOME(state, []))
                        val mctx = zapDjs mctx
                        fun rollThrough (failure, mctx) [] = continue failure (rctx, mctx) k
                          | rollThrough (failure, mctx) (dj :: djs) =
                              let val barrier1 = Barrier.new()
                                  val mctx1 = forceSingleton (mctx %% Barrier barrier1)
                                  val mctx1 = forceSingleton (mctx1 %% Prop dj)
                                  val failure__ = fn (mctx, errorMsg) => rollThrough (failure, mctx) djs    (* If case-split fails, try without splitting *)
                              in
                                  continue failure (rctx, mctx1)
                                    (fn (failure, mctx1X, elab) =>
                                     quantifyUpToBarrier (failure) mctx mctx1X barrier1
                                     (fn mctx =>
                                         let val barrier2 = Barrier.new()
                                             val mctx2 = forceSingleton (mctx %% Barrier barrier2)
                                         in
                                             continue failure (rctx, mctx2)
                                                      (fn (failure, mctx2X, elab) =>
                                                          quantifyUpToBarrier (failure) mctx mctx2X barrier2
                                                                              (fn mctx =>
                                                                                  rollThrough (failure, mctx) djs))
                                         end))
                              end
                    in
                        rollThrough (failure, mctx) djs
                    end
        end

    (* checkNoMemoCORE

      Applies SectI, TopI, AllI, UnivI, ImpliesI, ConjI as much as possible;
        then applies invertible left rules (ExisL, ConjL);
          then tries to apply non-invertible left rules (UnionL, BotL(??));
            finally (i.e. along each branch):
              calls checkNI.
    *)
    and checkNoMemoCORE failure (rctx : rctx, mctx : mctx) (e as (loc,exp), ppe as (path, pe)) t k =
        let val index = getIndex mctx
            val t = applyEquations mctx t
            val t = Inject.inject_type (lookupSorting rctx) t
            val _ = adprint (fn () => "++  check " ^ shortstr exp ^ "  against  " ^ t2str t)
(*????         val ctx as CTX{linear= linear, index= index, ...} = updateLinear ctx (zorch e) *)
            val freevars = freeLvars exp

            fun core_core (mctx, t) =
              let val _ = dprint (fn () => "core_core G = " ^ D.GammaToString (getG mctx))
                  val _ = dprint (fn () => "core_core t = " ^ t2str t)
                  val t = Inject.inject_type (lookupSorting rctx) t
                  val _ = dprint (fn () => "core_core*t = " ^ t2str t)
              in
                  case (isVal exp, t) of 
                   (true, Sect(A1,A2)) => 
                                (COVER "SectI";
                                 let val (A1, A2) = perm (A1, A2)
                                 in
                                    check failure (rctx, mctx $+ (Typecrumb(loc, A1))) (e, ppe) A1
                                      (fn (failure, mctx, elab1) => check failure (rctx, ($- mctx) $+ (Typecrumb(loc, A2))) (e, ppe) A2
                                      (fn (failure, mctx, elab2) => k (failure, $- mctx, (loc, Tuple[elab1, elab2]))))
                                 end)

                 | (true, Rsect(A1,A2)) => 
                                (COVER "RsectI";
                                 let val (A1, A2) = perm (A1, A2)
                                 in
                                    check failure (rctx, mctx $+ (Typecrumb(loc, A1))) (e, ppe) A1
                                      (fn (failure, mctx, elab1) => check failure (rctx, ($- mctx) $+ (Typecrumb(loc, A2))) (e, ppe) A2
                                      (fn (failure, mctx, elab2) => k (failure, $- mctx, overlay elab1 elab2)))
                                 end)

                 | (true, Top) => (COVER "TopI"; k (failure, mctx, e))

                 | (true, All(tvtv, uu, AA)) =>
                       let val tv = TV.new tvtv
                           val A = Types.substTypevar [(tvtv, Typevar tv)] AA
                           val _ = dprint (fn () =>"AllI INST " ^ t2str AA ^ " ====> " ^ t2str A)
                           val _ = COVER "AllI"
                       in
                           check failure (rctx, mctx +--+ (tv, NONE)) (e, ppe) A k
                       end

                 | (true, Univ(aa, sort, AA)) =>
                       let val a = IndexSym.new aa
                           val A = Types.substIndex [(aa, X.Uvar a)] AA
                           val _ = COVER "UnivI"
                           val _ = dprint (fn () => "Introducing Iall " ^ "original variable = " ^ IndexSym.toString aa ^ "; new variable = " ^ IndexSym.toString a ^ "")
                       in
                           check failure (rctx, forceSingleton (mctx %% Iall(a, sort))) (e, ppe) A k
                       end

                 | (_, Implies(P, B)) =>
                       let val barrier_id = Barrier.new()
                           val mctxP = forceSingleton (forceSingleton (mctx %% Barrier barrier_id) %% Prop P)
                       in
                           case getState mctxP of
                               NONE => k (failure, mctx, Context.elab_Bot loc rctx)  (* Rule (\Rcontra) *)
                             | SOME _ => (COVER "ImplI";
                                          check failure (rctx, mctxP) (e, ppe) B
                                                (fn (failure, mctxP, elab) =>
                                                    quantifyUpToBarrier (failure) mctx mctxP barrier_id
                                                                        (fn mctx => k (failure, mctx, elab))))
                       end


                 | (_, Conj(P, B)) =>
                       (COVER "ConjI";
                        && (failure) (mctx, P)
                           (fn mctx =>
                               check failure (rctx, mctx) (e, ppe) B k))
(* YYY XXX OK
                       check failure (rctx, mctx) (e, ppe) B k
*)

                 | (_, _) =>    (* Apply invertible left rules *)
                       let fun elimExises mctx preds [] =
                           (rctx, updateG mctx (fn _ => preds))
                             | elimExises mctx preds (foo :: linear) =
                               let in case foo of D.Linear(X, (tX, elabX)) =>
                                 let in case (MyList.contains X freevars, tX) of
                                     (true, Exis(aa, sort, AA)) =>
                                         let val _ = COVER "ExisL"
                                             val a = IndexSym.new aa
                                             val A = Types.substIndex [(aa, X.Uvar a)] AA
                                             val _ = dprint (fn () => "^^Eliminating " ^ IndexSym.toString aa ^ " --> " ^ IndexSym.toString a)
                                             val _ = print ("Apply invertible left rules (-exists _:" ^ Indexing.Sort.toString sort ^ "-)\n")
                                         in
                                             elimExises (forceSingleton (mctx %% Iall (a, sort))) preds (D.Linear(X, (A, elabX)) :: linear)
                                         end

                                   | (true, Conj(P, A)) =>
                                         (COVER "ConjL";
                                          elimExises
                                          (forceSingleton (mctx %% Prop P))
                                          preds (D.Linear(X, (A, elabX)) :: linear))   (* YYY OK *)

                                   |(_, _) => elimExises mctx (preds @ [foo]) linear
                                 end
                               | _ => elimExises mctx (preds @ [foo]) linear
                               end
                                   
                           val (rctx, mctx) = elimExises mctx [] (getG mctx)
                           
                           fun oblig preds [] = checkNI failure (rctx, mctx) (e, ppe) t k
                             | oblig preds (D.Linear(X, (tX, elabX)) :: linear) =
                                   let 
                                       val tX = substExtypevarNoAuto mctx tX

                                       fun doUnion (A, B) =
                                               let 
                                                   val _ = Counter.INC "unionLeftCount" unionLeftCount
                                                   val _ = adprint (fn () => "(%%% Union split begin; " ^ PV.toString X ^ " " ^ Int.toString (disjunctity tX) ^ " \\/s")
                                                   val _ = COVER "UnionL"
                                                   val (A, B) = perm (A, B)
                                                   val linearA = preds @ (D.Linear(X, (A, elabX)) :: linear)
                                                   val linearB = preds @ (D.Linear(X, (B, elabX)) :: linear)
                                                   val mctxA = updateG mctx (fn _ => linearA)

                                                   val barrierA = Barrier.new()
                                                   val mctxA1 = forceSingleton (mctxA %% Barrier barrierA)
                                               in
                                                   check failure (rctx, mctxA1) (e, ppe) t
                                                   (fn (failure, mctxA2, elab1) =>
                                                      (adprnt "%%% Union split: out of first disjunct";
                                                       quantifyUpToBarrier (failure) mctx mctxA2 barrierA
                                                       (fn mctx =>
                                                           let val barrierB = Barrier.new()
                                                               val mctxB = updateG mctx (fn _ => linearB)
                                                               val mctxB1 = forceSingleton (mctxB %% Barrier barrierB)
                                                           in
                                                               check failure (rctx, mctxB1) (e, ppe) t
                                                                     (fn (failure, mctxB2, elab2) => 
                                                                         (adprnt "%%% Union split: out of second disjunct";
                                                                          quantifyUpToBarrier (failure) mctx mctxB2 barrierB
                                                                                              (fn mctx => k (failure,
                                                                                                             mctx,
                                                                                                             (loc, Coercion.mkCase (Context.getDistinguished rctx)
                                                                                                                                   (loc, Sdml.Lvar X)
                                                                                                                                   (fn x1 => Subst.rename_locexp {from= X, to= x1} elab1,
                                                                                                                                    fn x2 => Subst.rename_locexp {from= X, to= x2} elab2))))))
                                                           end)))
                                               end

                                   in
                                       case (MyList.contains X freevars, tX) of
                                       (true, Union(A, B)) => doUnion (A, B)
                                     | (true, Runion(A, B)) => doUnion (A, B)
                                     | (true, Bot) => k (failure, mctx, Context.elab_Bot loc rctx)
                                     | _ => oblig (preds @ [D.Linear(X, (tX, elabX))]) linear
                                   end
                             | oblig preds (foo :: linear) = oblig (preds @ [foo]) linear
                       in
                           oblig [] (getG mctx)
                       end
(*******
                       let fun oblig idx preds Empty = (idx, [preds])
                                       | oblig idx preds (Ctx(X, tX, linear)) =
                                         let in case tX of
                                              Union(A, B) =>
                                         if MyList.contains X freevars then
                                                  let val _ = (dprnt ("\\/ Left --- " ^ shortstr exp ^ " --- "); message (fn()=> (pExp exp; nl())); dprnt "")
                                                      val _ = dprnt ("L e f t  " ^ PV.toString X ^ "")
                                                      val _ = Counter.INC "unionLeftCount" unionLeftCount
                                                      val (idx, oblig1) = oblig idx preds (Ctx(X, A, linear))
                                                      val (idx, oblig2) = oblig idx preds (Ctx(X, B, linear))
                                                  in
                                                      (idx, oblig1 @ oblig2   (* XXX XXX XXX*))
                                                  end else (let val _ = dprnt "ZZZ" in     oblig idx (Ctx(X, tX, preds)) linear   end)
                                            | Exis(aa, sort, AA) =>
                                                  let val a = IndexSym.new aa
                                                      val A = Types.substIndex [(aa, X.Var a)] AA
                                                  in
                                                      oblig (Iexists(a, sort) :: idx) preds (Ctx(X, A, linear))
                                                  end
                                            | Bot => (idx, [])   (* No obligations for bottom *)
                                            | _ => oblig idx (Ctx(X, tX, preds)) linear
                                          end

                                     val (idx, obligations) = oblig index Empty linear
                                   val _ = if length obligations > 1 then dprint (fn () => "OBLIG=\n" ^ Separate.list ";;;\n" (map (ctxtToString linearToString) obligations) ^ ";;;\n") else ()

                                     fun satisfy ctx [] = k (updateG ctx (fn _ => linear))
                                       | satisfy ctx (lin :: rest) = 
                                         let val _ = (*dprint (fn () => "=====satisfy:  "^ ctxToString (updateLinear ctx (fn _ => lin)) ^ "\n") *) ()  in
                                           checkNI failure (updateG ctx (fn _ => lin)) e t
                                              (fn ctx => satisfy ctx(*linear part will not be used*) rest)
                                         end
                                 in
                                     satisfy (updateIndex ctx (fn _ => idx)) obligations
          (*                         checkNI failure ctx e t k *)
                                 end
******)
              end

          val _ = dprint (fn () => "check core G = " ^ D.GammaToString (getG mctx))

          fun drillExtypevars (mctx, t) =              
                    case t of
                      Extypevar exalpha =>
                          let val _ = dprint (fn () => "check core Extypevar " ^ tv2str exalpha)
                          in case getEx mctx exalpha of
                                      UnknownEx => core_core (mctx, t)
                                   | SolvedEx solution =>
                                         let val _ = dprint (fn () => "check core Extypevar SolvedEx " ^ P.pTexp solution)
                                         in 
                                             drillExtypevars (substExtypevarAuto mctx solution)
                                         end
                                   | UnionEx solution =>
                                        let fun articulate () =
                                           let val exbeta = TV.new exalpha
                                           in
                                              core_core (solveExtypeArtic mctx exalpha [exbeta] (fn UnionEx solution => UnionEx(Union(solution, Extypevar exbeta))),
                                                              Extypevar exbeta)
                                           end
                                        in case exp of
                                           Fn _ => articulate ()
                                         | Tuple _ => articulate ()
                                         | Const _ => articulate ()
                                         | Con _ => articulate ()
                                         | Conapp _ => articulate ()
                                         | _ => core_core (substExtypevarAuto mctx t)
                                        end
                                   | SectEx solution =>
                                        core_core (substExtypevarAuto mctx t)
                          end
                    | _ => core_core (mctx, t)
        in
            drillExtypevars (mctx, t)
        end

    (* dropRctx : result -> (failure * mctx * result -> result)
                    -> (failure * (rctx * mctx) * coercion -> result) -> result *)
    and dropRctx elab k =
               fn (failure, (rctx, mctx), coercion) =>
                  let val _ = dprint (fn () => "dropRctx: coercion = " ^ Coercion.toString coercion)
                  in
                      k (failure,           mctx,  Coercion.compileWith (Context.getDistinguished rctx) coercion elab)
                  end

    (* checkNI

     Called at the "end(s)" of checkNoMemoCORE.
     If the expression to check is a synthesizing form, synthesize its type and check subtyping.
     Otherwise, call check'.
    *)
    and checkNI failure (rctx, mctx) (e as (loc,exp), ppe) t (k : result Context.failure * Context.mctx * result -> result)  =
        let val failure = fn stuff => checkLNI failure stuff (rctx, mctx) (e, ppe) t k
        in 
            if isSynth exp then
                (COVER "sub";
                infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (e, ppe)
                      (fn (failure, mctx, (tA, elab)) =>
                          let in
                              dprint (fn () => "subtype 1 ctx " ^ t2str tA ^ " <= " ^ t2str t ^ " ... ");
                              Subtype.subtype failure 1 (rctx, mctx) tA t (dropRctx elab k)
                          end)
                )
            else
                check' failure (rctx, mctx) (e, ppe) t k
        end

    (* true if, when checking e against a union type, might need to split the union
       at this point *)
    and fungible e = not (isSynth e)   (* if synthesizing, subtyping takes care of splitting *)
        andalso
        case e of
            Case _ => false   (* For terms such as Case, we can split later (inside each case arm) if required; splitting outside the Case is useless *)
          | Fn _ => true   (* Have to get to the arrow below the union *)
          | Conapp _ => true   (* Have to get to the d(i) below the union *)
          | RecordExp (_, exp) => true   (* Have to get to the record below the union *)
          | Tuple exps => true   (* ... the * ... *)
          | Merge exps => true  (* dyn.rml *)
          | Let _ => false   (* See above for Case *)
          | Lethint _ => false   (* See above for Case *)
          | LET(_, (_, boundExp), body) => fungible boundExp
          | LETSLACK(_, (_, boundExp), body) => fungible boundExp
          | Raise _ => false     (* Certainly not needed for Raise, which checks against any type *)
          | Handle _ => false   (* Can split inside *)
          | _ => raise Match

    
    (* check'
    
     Called by checkNI for checking forms. *)
    and check' failure (rctx, mctx) (le as (loc, e), ppe as (path, pe)) t k =
        let val _ = dprint(fn () => "check' ctx " ^ Location.toString loc ^ " <= " ^ t2str t ^ "")
            fun xxx () =
                case (e, pe, t) of
             (Var _, Path.Var, _) => raiseDead failure mctx loc (fn () => "check' Var IMPOSSIBLE!")  (* impossible *)
           | (Const _, Path.Const, _) => raiseDead failure mctx loc (fn () => "check' Const IMPOSSIBLE!")  (* impossible *)
           | (Fn (x, body),  Path.Fn (pbody),  Arrow(A, B)) => 
                 (dprint (fn () => "check' Fn: " ^ PV.toString x ^ ":" ^ t2str A
                         ^ " against " ^ t2str B ^ "");
                  Piper.echo (fn () => "% check Fn " ^ Location.toString loc ^ "\n");
                  frame mctx
                   (fn mctx => check failure
                                     ((*XXX should try to set empty somehow    (setLinearEmpty rctx) *) rctx,
                                      mctx ++ (x, substExtypevarNoAuto mctx A))
                                     (body, pbody)
                                     B)
                   (fn (failure, mctx, elab) => k (failure, mctx, (loc, Fn (x, elab))))
                 )
           | (Fn (x,body), Path.Fn (pbody), Extypevar exalpha) =>
                 let val exalpha1 = TV.fresh "articAbs1"
                     val exalpha2 = TV.fresh "articAbs2"
                     val arrow = Arrow(Extypevar exalpha1, Extypevar exalpha2)
                     val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            [exalpha1, exalpha2]
                                                            (fn UnknownEx => UnionEx arrow)
                 in
                   check' failure (rctx, articulatedMctx) (le, ppe) arrow k
                 end

              | (Leftanno(leftanno, e1 as (loc1,exp1)), Path.Leftanno pe1, C) =>
                    let 
                        val (pv, B) = case leftanno of
                                         LeftProgramVar (x, B) => (x, B)
                    in
                        case lookupOrd "ctxsubtype" mctx pv of
                                 (pv_texp, _) =>
                                     subtype failure 0 (rctx, mctx) pv_texp B
                                             (fn (failure, (_(*XXX*), mctx), coercion(*XXX*)) =>
                                                 check failure (rctx, mctx) (e1, pe1) C k)
                    end

           | (Tuple exps, Path.Tuple pexps, Product tAs) =>
                 if length exps = length tAs then
                     fold_elab failure
                               (rctx, mctx)
                               (fn (failure, mctx, locexps) => let val elab = (loc, Tuple locexps)
                                                                                    in
                                                                                       k (failure, mctx, elab)
                                                                                    end)
                               (fn (failure, mctx) =>
                                  fn (exp, tA) =>
                                    check failure (rctx, mctx) exp tA)
                               (ListPair.zip (ListPair.zip (exps, pexps), tAs))
                 else
                     raiseDead failure mctx loc (fn () => "check: " ^ Int.toString (length exps) ^ "-tuple against " ^ t2str t)
            
           | (RecordExp (fld1, fldExp), Path.RecordExp pexp, Record (fld2, fldA)) =>
                if fld1 = fld2 then
                    check failure (rctx, mctx) (fldExp, pexp) fldA
                       (fn (failure, mctx, elab) =>
                           k (failure, mctx, ( (* loc,  RecordExp*) ( (*fld1,*) elab))))
                else
                    raiseDead failure mctx loc
                              (fn () => "check: record expression field name `" ^ fld1
                                        ^ "' does not match record type " ^ t2str t)
           
           
           | (Merge exps, Path.Merge pexps, tA) =>
                   let fun try failure [] = raiseDead failure mctx loc (fn () => "check: a Merge against " ^ t2str tA)
                         | try failure (exp :: exps) =
                               check
                                  (fn _ => try failure exps)
                                  (rctx, mctx)
                                  exp
                                  tA
                                  k
                   in
                     try failure (ListPair.zip (exps, pexps))
                   end

           | (Tuple exps, Path.Tuple pexps, Extypevar exalpha) =>
                 let val exalphas = map (fn _ => TV.fresh "articChkProd") exps
                     val articulation = Product (map Extypevar exalphas)
                     val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            exalphas
                                                            (fn UnknownEx => UnionEx articulation)
                     val product = Product (map Extypevar exalphas)
                     val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            exalphas
                                                            (fn UnknownEx => UnionEx product)
                 in
                   check' failure (rctx, articulatedMctx) (le, ppe) product k
                 end

           | (Conapp(c,e2), Path.Conapp(pe2), t) =>
                 inferConapp failure (rctx, mctx) loc c t (fn (failure, mctx, ck, dom, cod) =>
                                         check failure (rctx, mctx) (e2, pe2) dom
                                         (fn (failure, mctx, elabArg) =>
                                             k (failure, mctx, (loc, Conapp (ck (* ! *), elabArg)))))

           | (Let(decs, locexp), Path.Let(pdecs, pexp), tB) =>
                 infer_decs failure (rctx, mctx) loc (ListPair.zip (decs, pdecs))
                       (fn (failure, (rctx', mctx'), elabDecs) =>
                           check failure ((*XXX setLinearEmpty*) rctx', mctx') (locexp, pexp) tB
                                     (fn (failure, mctx, elabBody) =>
                                         k (failure, mctx, (loc, Let(elabDecs, elabBody)))))

           | (Lethint(annos, locexp), Path.Lethint pexp, tB) =>
                 let val hintsToAdd = List.map (Basic.cross CC.shift Types.shift_universe) (*annos*) []   (*ZZZHINTS*)
                     val mctx = updateG mctx (D.addHints hintsToAdd)
                     (* val _ = dprint ("$$$$\n" ^ mctxToString mctx) *)
                 in
                     check failure (rctx, mctx) (locexp, pexp) tB k
                 end

           | (LET(X, locexp1, exp2), Path.LET(pexp1, pexp2), t) =>
                 infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (locexp1, pexp1)
                 (fn (failure, mctx, (tA, elab1)) =>
                     Context.frame mctx
                         (fn mctx =>
                             let val (mctx, tA) = substExtypevarAuto mctx tA
                             in
                                 check failure (rctx, mctx +- (X, (tA, NONE))) ((loc, exp2), pexp2) t
                             end)
                         (fn (failure, mctx, (_, elab2)) =>
                             k (failure, mctx, (loc, Let([(loc, Dec(X, ValKW, elab1))], (loc, elab2))))))

           | (LETSLACK(X, locexp1, exp2), Path.LETSLACK(pexp1, pexp2), t) =>
                 check failure (rctx, mctx +~~+ (X, (locexp1, pexp1))) ((loc, exp2), pexp2) t
                       (fn (failure, mctx, (_, elab2)) =>
                           let in case lookupLinear "LETSLACK-recover" mctx X of
                                      (_, SOME elab1) =>
                                             k (failure, mctx, (loc, Let([(loc, Dec(X, ValKW, elab1))], (loc, elab2))))
                           end)

           | (Case(locexp, arms), Path.Case(pexp, parms), t) =>
                  infer failure WANT_ORDINARY_TYPE (rctx, mctx) (locexp, pexp)
                        (fn (failure, mctx, (A, elabScrutinee)) =>
                            let val failure = PRfailure failure "Case"

                                val zipped = ListPair.zip (arms, parms)
                                             
                                fun splitFn c =
                                    List.map (fn (conjunct, conjunctType) => conjunct) (lookupConjuncts "Case_splitFn" rctx c)
                                
                                fun splitArm (Arm (pattern, locexp), path) =
                                    let 
                                        val _ = cdprint (fn () => "Case: splitArm: source pattern: " ^ patternToString pattern)
(*                                        val patterns = Patterns.splitIntoConjuncts splitFn pattern
                                        val _ = dprint (fn () => "Case: splitArm: split patterns: " ^ Separate.list " | " (List.map patternToString patterns))
                                        val arms = List.map (fn pattern => (Arm (pattern, locexp), path)) patterns
                                        val len = List.length arms
                                        val _ = print ("source arm has " ^ Int.toString len ^ " splits\n")
                                        val _ = print ("they are:\n")
                                        val _ = List.app (fn (Arm (pattern, _), _) => print (patternToString pattern ^ "\n")) arms
*)
                                        val patterns = Patterns.splitIntoConjuncts splitFn pattern
                                        val arm = (fn pattern => (Arm (pattern, locexp), path)) patterns
                                        val _ = cdprint (fn () => "Case: splitArm: split pattern: " ^ patternToString pattern)
                                        val _ = cdprint (fn () => "source arm has weight " ^ Int.toString (Patterns.weight patterns))
                                    in
                                        arm  (* arms *)
                                    end

                                val splitArms = List.map splitArm zipped
(*
                                val splitArms = List.concat (List.map splitArm zipped)
                                val len = List.length splitArms
                                val _ = print ("source arms have total of " ^ Int.toString len ^ " splits\n")
*)
                            in
                                check_arms failure
                                           (rctx, mctx)
                                           A
                                           (splitArms,
                                            [])
                                           WildPattern
                                           t
                                           loc
                                           (fn (failure, mctx, elabArms) =>
                                               k (failure, mctx, (loc, Case(elabScrutinee, elabArms))))
                            end)
           | _ => raiseDead failure mctx loc (fn () => "check' 2")
                  
            fun doUnion (A1, A2) =
                  let val (A1, A2) = perm (A1, A2)
                      val distinguished = Context.getDistinguished rctx
                      val _ = Context.checkSolverState "check Union 1" mctx
                      val _ = adprint (fn () => "++  Checking against union  " ^ t2str t ^ "; checking first branch") 
                      val failure = fn _ =>
                                       let val _ = adprint (fn () => "++  Checking against second branch: " ^ t2str A2 ^ "")
                                           val _ = Context.checkSolverState "check Union 2" mctx
                                       in
                                           check failure (rctx, mctx) (le, ppe) A2
                                              (fn (failure, mctx, elab2) => k (failure, mctx, (loc, Conapp (#inr_pv distinguished, elab2))))
                                       end
                  in
                      check failure (rctx, mctx) (le, ppe) A1
                                 (fn (failure, mctx, elab1) => k (failure, mctx, (loc, Conapp (#inl_pv distinguished, elab1))))
                  end
        in
            case (fungible e, t) of
                (true,  Union(A1, A2)) => doUnion (A1, A2)
              | (true,  Runion(A1, A2)) => doUnion (A1, A2)

              | (true,  Exis(aa, sort, AA)) =>
                                      let val a = IndexSym.new aa
                                          val A = Types.substIndex [(aa, X.Evar a)] AA
                                      in
                                          check failure (rctx, forceSingleton (mctx %% Iexists(a, sort))) (le, ppe) A k
                                      end
              | _ => xxx()
        end

(*
  - Decompose only "left-useful" types:

     Useful ::= Useful & B     --Decompose only left component, if B not Useful
                 | A & Useful     --Decompose only right component, if A not Useful
                 | A \/ B    --INVERTIBLE, handled in `check'
                 | -all a:y- Useful     --Strip quantifier only if quantified type is Useful
                 | -exists b:y- B    --INVERTIBLE, handled in `check'
                 | bot        --INVERTIBLE, handled in `check'

      benefit: Need not decompose intersections of ordinary types

  - Use an ephemeral hash table to store type information; make a new empty hash table
     when a root is encountered
  OR
  - Add texp-cell to Lvar
  (Either alternative painful in (\Rsectintro) -- need to checkpoint state)
*)
    and checkLNI_X failure stuff (rctx, mctx) (locexp as (loc, _), ppe as (path, pe)) t k =
        let
            fun useful (Sect(A, B)) = useful A orelse useful B
              | useful (Rsect(A, B)) = useful A orelse useful B
              | useful (Univ(_, _, A)) = useful A
              | useful (Implies(_, A)) = useful A

              | useful (Bot) = true
              | useful (Union _) = true
              | useful (Runion _) = true
              | useful (Exis _) = true
              | useful (Conj _) = true

              | useful _ = false

            fun aux failure preds [] = failure stuff
              | aux failure preds (D.Linear(X, (tX, elabX)) :: linear) =
                    let
                        fun doIntersection (A, B) =
                             let val (A, B) = perm (A, B)
                                 fun tryParts stuff = 
                                     let fun tryB stuff =
                                         if useful B then
                                           (  print "checkLNI_X: trying rule \\Rleftsect{2}\n"; Counter.INC "sectLeftCount" sectLeftCount;
                                              check failure (rctx, updateG mctx (fn _ => preds @ (D.Linear(X, (B, elabX)) :: linear))) (locexp, ppe) t k  )
                                         else
                                             failure stuff
                                     in
                                         if useful A then
                                           (  print "checkLNI_X: trying rule \\Rleftsect{1}\n"; Counter.INC "sectLeftCount" sectLeftCount;
                                              check tryB (rctx, updateG mctx (fn _ => preds @ (D.Linear(X, (A, elabX)) :: linear))) (locexp, ppe) t k  )
                                         else
                                             tryB stuff
                                     end
                             in
                                 aux tryParts (preds @ [D.Linear(X, (tX, elabX))]) linear
                             end
                    in
                       case tX of
                           Sect(A, B) => doIntersection(A, B)
                         | Rsect(A, B) => doIntersection(A, B)
    (*
                                  let fun checkpart failure part =
                                          check failure (updateG rctx (fn _ => preds @@@ (Ctx(X, part, linear))), mctx) (locexp, ppe) t k
                                  in
                                      if useful A then (checkpart (fn stuff =>
                                                                      if useful B then checkpart failure B
                                                                      else failure stuff)
                                               A)
                                      else
                                          if useful B then checkpart failure B
                                          else raiseDead' failure mctx loc (fn () => "checkL Sect")
                                  end
    *)
                         | _ => aux failure (preds @ [D.Linear(X, (tX, elabX))]) linear
                     end
              | aux failure preds (foo :: linear) = aux failure (preds @ [foo]) linear
        in
            aux failure D.empty (getG mctx)
        end

    and checkLNI failure stuff (rctx, mctx) (locexp as (loc, _), ppe as (path, pe)) t k =
        let fun ending failure original _ = failure original

            fun slack_aux failure original preds (X, expX) slack kRoll =
                let val _ = dprint (fn () => "De-slacking " ^ PV.toString X)
(*                     val _ = dprint (fn () => "Slack : " ^ ctxtToString slackToString (preds @@@ slack)) *)
                     val mctx' = updateG mctx (fn _ => preds @ slack)
                     val failure = fn stuff => kRoll {newPrev= preds @ [D.Slack(X, expX)]}
                 in
                     infer failure MAINTAIN_PRINCIPALITY (rctx, mctx') expX
                     (fn (failure, mctx, (texp, elabSlack)) =>
                      let (* val _ = dprint (fn () => "Linear: " ^ ctxtToString linearToString (getLinear (rctx' +- (X, texp)))) *)
                         (* val _ = dprint (fn () => "                                                slack") *)
                      in
(*                          check failure (rctx' +- (X, texp), mctx) (locexp, ppe) t k    *)
                            check failure (rctx, mctx +- (X, (substExtypevarNoAuto mctx texp, SOME elabSlack))) (locexp, ppe) t k
                      end)
                 end
        in
            checkLNI_X
                (fn stuff => D.roll (fn d => let in case d of D.Slack stuff => SOME stuff | _ => NONE end)
                                        (ending failure stuff)
                                        (slack_aux failure stuff)
                                        (getG mctx))
                stuff (rctx, mctx) (locexp, ppe) t k
        end

    and check_annotation failure (rctx, mctx) loc anno k =
        case anno of
            [] => raiseDead failure mctx loc (fn () => "check_annotation")
          | anno :: typings =>
                let 
                    fun toCtxanno G0 anno = case anno of

                        AnnotationType.Type A => (G0, A)
                        
                      | AnnotationType.LeftProgramVar (x, A, anno) =>
                           toCtxanno (G0 @ [CC.ProgramVar (x, A)]) anno
                           
                      | AnnotationType.Some (a, sort, anno) =>
                           toCtxanno (G0 @ [CC.IndexVar (a, sort)]) anno
                    
                    val (G0, A0) = toCtxanno [] anno
                    val _ = print ("Typecheck.check_annotation: \n"
                                  ^ "   " ^ "G0 = " ^ Print.p Print.printConcContext G0 ^ "\n"
                                  ^ "   " ^ "A0 = " ^ Print.pTexp A0 ^ "\n\n")
                    val A0 = Inject.inject_type (lookupSorting rctx) A0
                in
                    Subtype.ctxsubtype (fn _ => check_annotation failure (rctx, mctx) loc typings k)
                               (rctx, mctx)
                               (G0, A0)
                               (fn (failure, mctx, A) => 
                                   (dprint(fn () => "++  check_annotation " ^ Location.toString loc ^ ": " ^ t2str A ^ "\n" ^ ctxToString (rctx, mctx));
                                    k (failure, mctx, A)))
                end
(*
        case anno of
            [] => raiseDead failure mctx loc (fn () => "check_ctxanno")
          | (G0, A0) :: typings =>
                let 
                    val A0 = Inject.inject_type (lookupSorting rctx) A0
                in
                    Subtype.ctxsubtype (fn _ => check_ctxanno failure (rctx, mctx) loc typings k)
                               (rctx, mctx)
                               (G0, A0)
                               (fn (failure, mctx, A) => 
                                   (dprint(fn () => "++  check_ctxanno " ^ Location.toString loc ^ ": " ^ t2str A ^ "\n" ^ ctxToString (rctx, mctx));
                                    k (failure, mctx, A)))
                end
*)

(*
 * Tangled and horrible code to check case expressions.
 *
 * "Structure":
 *
 *   check_arms
 *       `--> check_pattern
 *            `--> build_pattern_tracks
 *)

 (* check_arms *)
 (*   Clause for no remaining branches *)
    and check_arms failure
                    (rctx, mctx : mctx)
                    datatexp
                    ([] (* remaining arms *),
                     elab_arms)
                    domain
                    t
                    loc
                    k
      =
            let
                val _ = print ("check_arms ... [] at " ^ Location.toString loc ^ "\n")
            in
                case domain of
                      OrPattern [] =>     (* nothing left in domain *)
                             (* Succeed, passing on elaborated arms *)
                               k (failure, mctx, elab_arms)
                 |
                      domain =>  (* some patterns remaining *)
                         let 
                             val failureFn = 
                                 (* some remaining pattern is possible: Match is nonexhaustive. *)
                                     fn failureX =>
                                     fn _ => (print "Match may be nonexhaustive2\n";
                                                     raiseDead failure (* Possibly this should be an "outer" failure continuation. *)
                                                                       mctx loc (fn () => "Match nonexhaustive"))
                             val continueFn =
                                 (* check_pattern has shown remaining patterns to be impossible *)
                                     fn (failure, mctx, new_elab_arms) =>
                                        k (failure, mctx, elab_arms @ new_elab_arms)
                         in
                             (* print ("check_arms NONEXHCHECK\n"); *)
                             (* Try to show that remaining patterns are impossible *)
                             check_pattern failure
                                          ((rctx, mctx), datatexp, loc, domain, failureFn, continueFn)
                         end
            end


  (*   Clause for some branch remaining *)
      | check_arms failure
                    (rctx, mctx)
                    datatexp
                    ((Arm(pattern, locexp as (loc,_)), Path.Arm pexp)  ::  arms,
                     elab_arms)
                    domain
                    t
                    _ (* location of case expression; location of head Arm takes priority *)
                    k
        =

            let val _ = cdprint (fn () => D.GammaToString (getG mctx))
               val _ = cdprint (fn () => "check_arm (" ^ Location.toString loc ^ "): split pattern: " ^ patternToString pattern)
               
               fun checkFn failure (mctxQ, rctxArm, barrier_id, checkFnK) =
                    let 
                        val _ = print ("Checking case arm at " ^ Location.toString loc ^ " against type " ^ t2str t ^ "\n")
                        val _  = Piper.echo (fn () => "% case arm at " ^ Location.toString loc ^ " against type " ^ t2str t ^ "\n");

                        val _ = Counter.INC "caseArmChecked" caseArmChecked
                        val _ = cdprint (fn () => "Checking case arm...\n"
                                                 ^ "Against: " ^ t2str t ^ "\n"
(*                                                 ^ "Under rctxArm = [[[ " ^ rctxToString rctxArm 
                                                 ^ "]]]\n"
                                                 ^ "Under mctxQ = [[[ " ^ mctxToString mctxQ ^ "]]]."
*)
                                        )
                        val _ = Context.checkSolverState "Typecheck.check_arm.checkFn" mctxQ
                    in

                           if
Context.isSolved (rctx, mctxQ) then
                               let
                                   val _ = PRINT ("Context solved before trying to check case arm" ^ "" ^ "\n")
                               in
                                   check (fn arg => (cdprnt ("Case arm check failed"); failure arg)) (rctxArm, mctxQ) (locexp, pexp) t
                                         (fn (failureAfter, mctxInArm, elab) =>
                                             quantifyUpToBarrier failure(*previous failure!*) mctx mctxInArm barrier_id
                                                  (fn mctxZ =>
                                                      if Context.isSolved (rctx, mctxInArm)
                                                      then
                                                          let val _ = PRINT ("Independence used for " ^ "case arm" ^ "\n")
                                                          in
                                                              checkFnK (failure(*!*), mctxZ (*!?*), elab)
                                                          end
                                                      else
                                                          checkFnK (failureAfter, mctxZ, elab))
                                         )
                               end

                           else

                               check failure (rctxArm, mctxQ) (locexp, pexp) t
                                     (fn (failureAfter, mctxInArm, elab) =>
                                         quantifyUpToBarrier failureAfter mctx mctxInArm barrier_id
                                                             (fn mctxZ => checkFnK (failureAfter, mctxZ, elab)))
                    end

               fun otherCtors conjunct = 
                     let
                         val owner = Context.getConjunctOwner rctx conjunct
                         val coninfo as Coninfo{allcons, ...} = lookupConinfo "check_arm.::.otherCtors" rctx owner
                         fun getConjuncts nullary c = List.map (fn (conjunct, conjunctType) => (conjunct, nullary))
                                                               (lookupConjuncts "check_arm.::.otherCtors" rctx c)
                         val conjuncts = List.concat (List.map (fn (c, nullary) => getConjuncts nullary c) allcons)
                     in
                         List.filter (fn (conjunct', nullary) => conjunct' <> conjunct) conjuncts
                     end

               val (domain (*remaining part of domain, after subtracting `pattern'*),
                    pattern_sect (*relevant part of `pattern', i.e. intersection with original domain*))
                    =
                    Patterns.analyze otherCtors (domain, pattern)

(*               val patterns = MyList.elimDups patterns    doesn't help*)
               val _ = cdprint (fn () => "Analyzed intersection of " ^ patternToString pattern ^ ":\n"
                                         ^ patternToString pattern_sect
                                         ^ "\nEnd patterns.\n")

               (* val _ = print ("A(" ^ Int.toString (Patterns.weight pattern_sect) ^ ")A ") *)
               val pattern_sect = Patterns.improve pattern_sect
               (* val _ = print ("B(" ^ Int.toString (Patterns.weight pattern_sect) ^ ")B ") *)
               val _ = cdprint (fn () => "IMPROVED version of " ^ patternToString pattern ^ ":\n"
                                         ^ patternToString pattern_sect
                                         ^ "\nEnd patterns.\n"
                                         ^ "Remaining domain: "^ patternToString domain ^ "\n")

(*               val domain = MyList.elimDups domain    hurts a lot *)
               (* val _ = print ("D(" ^ Int.toString (Patterns.weight domain) ^ ")D ") *)
               val domain = Patterns.improve domain
               (* val _ = print ("E(" ^ Int.toString (Patterns.weight domain) ^ ")E ") *)
               val _ = cdprint (fn () => "Pattern to be checked: "^ patternToString pattern_sect ^ "\n")

               fun continue (failure, mctx, new_elab_arms) =
                     check_arms failure
                                 (rctx, mctx) 
                                 datatexp
                                 ( (* tail *) arms,
                                  elab_arms @ new_elab_arms)
                                 domain
                                 t
                                 loc
                                 k
            in
                check_pattern failure ((rctx, mctx), datatexp, loc, pattern_sect, checkFn, continue)
            end
          

   and PRfailure failure s =
       fn stuff => ( (* print (s ^ " FAIL.\n"); *) failure stuff)


(* check_pattern
 *
 *    Given `pattern' and a `checkFn' (ADD TYPE ANNOTATION),
 *     call `build_pattern_tracks' to build a set of "tracks" TRK(texp, (rctx, mctx)),
 *     then call `checkFn' on each.
 *
 *    The details (adding a Barrier to separate out the new assumptions, etc.)
 *     need to be documented.
 *)
   and check_pattern failure ((rctx, mctx),
                              datatexp,
                              loc,
                              pattern,
                              checkFn,
                              continue : result failure * mctx * arm list  -> result)
       =
        let val failure = PRfailure failure "check_pattern"

            val _ = print ("check_pattern (" ^ Location.toString loc ^ "): pattern  " 
                           ^ patternToString pattern  ^ " : " ^ t2str datatexp ^ "\n")
                    
            val _ = check_pattern_now := !check_pattern_now + 1
            val me = !check_pattern_now
            
            val barr = Barrier.new()
            val mctxB = forceSingleton (mctx %% Barrier barr)
        in
            build_pattern_tracks failure loc (TRK (pattern, datatexp, (rctx, mctxB)))
                (fn (failure, tracks : track list) =>
                    let (* val _ = print ("check_pattern:  tracks: " ^ tracksToString tracks ^ ".\n") *)
                       (* roll:
                        Call checkFn for the given track.
                  *)
                       fun roll failure (TRK (pattern, texp, (rctx, mctx))) (kSucc : result failure * mctx * arm list -> result) mctxZ =
                            let val mctxQ = mctx
                            in
                                case getState mctxQ of
                                    NONE => (print ("check_pattern: TRK(" ^ patternToString pattern ^ ", _, _): getState NONE\n");
                                             kSucc (failure, mctxZ, []))
                                  | SOME _ => 
                                        let
                                            val _ = cdprint (fn () => "% checking pattern: " ^ patternToString pattern ^ " which has type " ^ t2str texp)
                                            val _ = cdprint (fn () => "% mctx: " ^ mctxToString mctx)
                                        in
                                            checkFn failure (mctxQ, rctx, barr,
                                                             fn (failure, mctxZ, elabExp) => kSucc (failure, mctxZ, [Arm(pattern(*from TRK*), elabExp)]))
                                        end
                            end
                       val roll = roll : result failure -> track -> (result failure * mctx * arm list -> result) -> mctx -> result

                       fun unionizeArms (old, new) = case (old, new) of
                           (old, []) => old
                         | ([], new) => new
                         | (old, _) => old
                            
                       (* rollAll:
                         `roll' each track, building up elab_arms.
                  *)
                       val trackCounter = ref 0
                       fun rollAll failure tracks elab_arms mctxZ = case tracks of
                           [] => continue (failure, mctxZ, elab_arms)
                         | track :: rest => (print ("roll (#" ^ Int.toString me ^ "): checking track " ^ Int.toString (trackCounter := !trackCounter +1; !trackCounter)
                                                    ^ " of " ^ Int.toString (List.length tracks + !trackCounter - 1)
                                                    ^ ": " ^ trackToString track ^ "\n");
                                               roll failure track (fn (failure, mctxZ, new_elab_arms) =>
                                                                      ( (*print ("check_pattern: TRACK OK: " ^ trackToString track ^ "\n"); *)
                                                                            rollAll failure rest (unionizeArms (elab_arms, new_elab_arms)) mctxZ)) mctxZ)
                       val _ = print ("roll (#" ^ Int.toString me ^ "): " ^ Int.toString (List.length tracks) ^ " tracks to roll\n")
                in
                    rollAll failure tracks [] mctx
                end)
        end


 (* build_pattern_tracks:
  *       Given `pattern' and a single "track" TRK(p, A, ctx), where `ctx' has a fresh Barrier,
  *        call continuation k with a *list* of tracks,
  *        *all* of which need to "go through".
  *
  *       The case branches themselves are *not* checked by build_pattern_tracks;
  *        see `check_pattern'.
  *)
    and build_pattern_tracks failure (loc)
                      (TRK (pattern, A, ctx as (rctx, mctx : mctx)))
                      (k : result failure * (track list) -> result)
        =
        let val k = fn (failure, tracks) => ((*print ("build_pattern_tracks returning tracks: " ^ tracksToString tracks ^ "\n");*) k (failure, tracks))
            val build_pattern_tracks = fn failure => build_pattern_tracks failure (loc)
            val failure = fn stuff => ((*print "build_pattern_tracks FAILING\n"; *)failure stuff)
            
            fun addBindingToTrack x (TRK (pattern, A, (rctx, mctx))) =
                TRK (pattern, A, (rctx, mctx ++ (x, substExtypevarNoAuto mctx A)))
            fun modifyPattern patfunction (TRK (pattern, A, ctx)) =
                TRK(patfunction pattern, A, ctx)
            
            val (mctx, A) = applyEx (mctx, A)  (* XXX5 *)
            val A = Inject.inject_type (lookupSorting rctx) A
            
            val _ = pprint (fn () => "build_pattern_tracks (" ^ sINC build_pattern_tracks_now ^ "): input pattern: " ^ patternToString pattern)
(*            val _ = pprint (fn () => "..." ^ (if Context.consistent mctx then "consistent" else "INCONSISTENT :-)")) *)
        in
            case (pattern, A) of
                (VarPattern x, A)  => 
                    let (* val _ = print ("VarPattern " ^ PV.toString x ^ "\n") *)
                    in
                        build_pattern_tracks failure (TRK (AsPattern(x, WildPattern), A, ctx)) k
                    end
              
              | (WildPattern, A) => 
                    k (failure, [TRK (WildPattern, A, ctx)])

              | (OrPattern [], A) =>   (* empty (unsatisfiable) pattern; never matches, so yields no obligations *)
                    k (failure, [])

              | (OrPattern (p1 :: ps), A) => 
                    build_pattern_tracks failure (TRK (p1, A, ctx))
                       (fn (failure, stuff1) =>
                           build_pattern_tracks failure (TRK (OrPattern ps, A, ctx))
                              (fn (failure, stuff2) =>
                                  k (failure, stuff1 @ stuff2)))

              | (AsPattern(x, pat0), A) =>
                    build_pattern_tracks failure (TRK (pat0, A, ctx))
                      (fn (failure, stuff) => k (failure, List.map (addBindingToTrack x  o  modifyPattern (fn pat0 => AsPattern(x, pat0))) stuff))
(*            | (pattern, Sect(A1, A2)) =>
 XXX to be implemented
*) 
              | (pattern, Univ(bb, sort, BB)) =>
                    let val b = IndexSym.new bb
                        val B = Types.substIndex [(bb, X.Uvar b)] BB
                        val _ = print ("build_pattern_tracks:(_, Univ(" ^ IndexSym.toString bb ^ "-->" ^ IndexSym.toString b
                                     ^ ": " ^ X.Sort.toString sort ^ ". " ^ t2str BB ^ "))\n")
                    in
                       build_pattern_tracks failure
                        (TRK (pattern, B, (rctx, forceSingleton (mctx %% Iall(b, sort)))))
                        (fn (failure, tracks) =>
                            let val tracks' = map (fn (TRK (pattern, texp_i, Xi_i)) => TRK (pattern, Univ(b, sort, texp_i), Xi_i)) tracks
                            in
                                k (failure, tracks)
                            end)
                    end
              
              | (pattern, All(bb, uu, BB)) =>   (*XXX*) (*I haven't really thought this through; I just aped the Univ case. *)
                    let val _ = print "triggered\n"
                        val b = TV.new bb
                        val B = Types.substTypevar [(bb, Typevar b)] BB
                    in
                        build_pattern_tracks failure
(*                        (TRK (B, (rctx, addExtype (mctx +--+ b) b))) *)
                        (TRK (pattern, B, (rctx, mctx +--+ (b, NONE))))
                        (fn (failure, tracks) =>
                            let val tracks' = map (fn (TRK (pattern, texp_i, Xi_i)) => TRK (pattern, All(b, uu, texp_i), Xi_i)) tracks
                            in
                                k (failure, tracks)
                            end)
                    end

(*            | (pattern, Exis(bb, sort, BB)) => 
              | (pattern, Conj(P, A)) => 
 XXX to be implemented
*)
              | (pattern, Union(A1, A2)) =>
                      build_pattern_tracks failure (TRK (pattern, A1, ctx))
                      (fn (failure, tracks1) =>
                          build_pattern_tracks failure (TRK (pattern, A2, ctx))
                          (fn (failure, tracks2) =>
                              k (failure, tracks1 @ tracks2)))

              | (pattern, Runion(A1, A2)) =>
                      build_pattern_tracks failure (TRK (pattern, A1, ctx))
                      (fn (failure, tracks1) =>
                          build_pattern_tracks failure (TRK (pattern, A2, ctx))
                          (fn (failure, tracks2) =>
                              k (failure, tracks1 @ tracks2)))

              | (StringPattern s, A) =>
                    let in case A of
                        Tycon(tc, _, []) => if tc = #stringTC(Context.getDistinguished rctx) then
                                               k (failure, [TRK (StringPattern s, A, ctx)])
                                               else fail ("string pattern \"" ^ s ^ "\" used with non-string type " ^ t2str A)
                      | _ => fail ("string pattern \"" ^ s ^ "\" used with non-string type " ^ t2str A)
                    end

              | (IntPattern i, A) =>
                    let in case A of
                        Tycon(tc, _, []) =>
                               if tc = #intTC(Context.getDistinguished rctx) then
                                   k (failure, [TRK (IntPattern i, A, ctx)])
                               else (* fail ("int pattern `(" ^ Int.toString i ^ ")' used with non-int type " ^ t2str A) *)
                                        k (failure, [])
(*                      | Exis(a, sort, A0 as Tycon(tc, _, [])) =>
                             build_pattern_tracks failure pattern (A0, ctx) k *)
                      | _ => k (failure, [])
                                 (* fail ("int pattern `(" ^ Int.toString i ^ ")' used with non-int type " ^ t2str A) *)
                    end

              | (TuplePattern [], A) =>
                    let in case A of
                        Product [] => k (failure, [TRK (TuplePattern [], A, ctx)])
                      | _ => fail "unit value pattern `()' used with non-unit type"
                    end
              | (tuplepattern as TuplePattern (pats as _ :: _), A) =>
                    let (* val _ = print ("`````TuplePattern(" ^ Separate.list ", " (map patternToString pats) ^ ") against " ^ t2str A ^ "\n") *)
                    in
                      case A of
                        Product (texps as _ :: _) => 
                              let val pattexps = (ListPair.zip (pats, texps)) handle ListPair.UnequalLengths => fail ("tuple pattern has wrong arity")
                                  fun build (failure,
                                             (*accumulator*) (ctxtexpslist : (ctx * ((pattern * texp) list)) list),
                                             pattexps) k =
                                      case pattexps of
                                          [] => k (failure, List.map (fn (ctx, pat_texps) =>
                                                                         let val (patterns, texps) = ListPair.unzip pat_texps
                                                                             val texp = Product (List.rev texps)
                                                                         in TRK (TuplePattern (List.rev patterns), texp, ctx) end) ctxtexpslist)
                                        | (pat, texp) :: rest =>
                                              let fun walk (failure, acc) ctxtexpslist = case ctxtexpslist of
                                                          [] => build (failure, acc, rest) k
                                                        | (ctx, pat_texps) :: rest =>
                                                             let in
                                                                build_pattern_tracks failure (TRK (pat, texp, ctx))
                                                                    (fn (failure, tracks) =>
                                                                        walk (failure, (List.map (fn (TRK (patX, texpX, ctxX)) => (ctxX, (patX, texpX) :: pat_texps)) tracks) @ acc) rest)
                                                             end
                                              in
                                                  walk (failure, []) ctxtexpslist
                                              end
                              in
                                  build (failure, [(ctx, [])], pattexps) k
                              end
                      | A => fail ("tuple pattern " ^ patternToString tuplepattern  ^ " does not match type: " ^ t2str A)
                    end

              
              | (wholepat as CtorPattern (c, pat0), A) => 
                    let val _ = cdprint (fn () => "build_pattern_tracks: CtorPattern " ^ patternToString wholepat ^ " : " ^ t2str A)
                        val tuples = caseCon rctx loc (c, Context.getConjunctType rctx c) pat0 A
                        val _ = cdprint (fn () => "build_pattern_tracks: caseCon returned TUPs:\n" ^ tuplesToString tuples)
                        (* val _ = print ("Number of datasort-weeded tuples:"
                                          ^ Int.toString (List.length tuples) ^ "\n")*)
                        val time1 = Time.now()
                        
                    in
                        collect mctx A tuples
                        (fn filteredTuples =>    (* tuples corresponding to constructor branches with datasort- and index-compatible codomains *)
                            let
                                (*
                                val collectTime = Time.-(Time.now(), time1)
                                val time = Time.toReal collectTime * 1000000.0  (* convert to microseconds *)
                                val _ = if time > 100.0 then
                                            print ("<" ^ Real.toString time ^ ">")
                                        else ()
                                 *)
                            in 
                                (*                        let fun otherToString (TUP(_, assns'', _, _, cod'')) =
            (" (" ^ indexToString assns'' ^ "; ... ; cod'' = " ^ t2str cod'' ^ ") ")
        val _ = print ("filteredTuples ---> " ^ Separate.list ";;;\n"
                       (map (fn (otherTuples, (rctx, mctx), domOpt, cod) =>
                                ("<< cod= " ^ t2str cod ^ ", " ^ "{" ^ Separate.list ", " (map otherToString otherTuples) ^ "}, ... >>"))
                        filteredTuples)   ^ "\n\n") *)
                                
                                if List.null filteredTuples then
                                    k (failure, [])
                                else
                                    let
                                        (* val _ = print ("<X>" ^ Int.toString (List.length filteredTuples) ^ "\n") *)
                                                      
                                        (* Strip every tuple x with domain below some other tuple. *)
                                        fun optimize tuples =
                                            let 
                                                val tuples = Array.fromList (List.map SOME tuples) 
                                                     (* For constant-time deletion, and simplification *)
                                                fun fastIncompleteSubtype s1 s2 =
                                                       let fun f (s1, s2) = case (s1, s2) of
                                                                (Product A1s, Product A2s) =>     (List.length A1s = List.length A2s) andalso (List.all f (ListPair.zip (A1s, A2s)))
                                                              | (Tycon(tc1, i1, []), Tycon(tc2, i2, [])) =>          (i1 = i2)  andalso  (  tc1 = tc2  orelse  DS.blitheSubsort(tc1, tc2)  )
                                                              (*PPP*) (* Need polymorphic case (devolve to fastIncompleteSubtype with appropriate variances on each...) *)
                                                              | (Exis(a1, sort1, A1), Exis(a2, sort2, A2)) =>   (sort1 = sort2) andalso
                                                                                                                                                  let val A2' = Types.substIndex [(a2, X.Evar a1)] A2
                                                                                                                                                  in f (A1, A2') end
                                                              | (_, _) => false   (*PPP*) (* print warning? *)
                                                       in
                                                           f (s1, s2)
                                                       end

                                                fun pound ((n1, INTUP{previous= otherTuples1, ctx= ctx1, varmap= varmap1, conjunct= conjunct1, domainOpt= domOpt1, codomain= cod1}),
                                                           (n2, INTUP{previous= otherTuples2, ctx= ctx2, varmap= varmap2, conjunct= conjunct2, domainOpt= domOpt2, codomain= cod2})) =
                                                                  case (domOpt1, domOpt2) of
                                                                      (SOME dom1, SOME dom2) =>
                                                                          if fastIncompleteSubtype dom1 dom2 then
                                                                              (* Strip first tuple *)
                                                                                  (print " [pound] ";
                                                                                   Array.update (tuples, n1, NONE))
                                                                          else ()
                                                                    | _ => ()
                                            in
                                                Case.allDistinctPairs pound tuples;
                                                List.mapPartial (fn x => x) (Array.foldl (op ::) [] tuples)
                                            end (* fun optimize *)
                                        
                                        val _ = cdprint (fn () => "List.length(filteredTuples) = " ^ Int.toString (List.length filteredTuples))
                                        val optimizedTuples = optimize filteredTuples
                                        val _ = cdprint (fn () => "optimizedTuples = {\n" ^
                                                                  intupsToString optimizedTuples)
                                        
                                        fun build failure (Xis : xi_track list) prev_tuples tuples k =
                                            case tuples of
                                                [] =>
                                                    let  (* val _ = print ("length(Xis) = " ^ Int.toString(List.length Xis) ^ "\n") *)
                                                        val TRKs = List.map (fn XITRK(patternOpt, c, A, ctx) => TRK (CtorPattern (c, patternOpt), A, ctx)) Xis
                                                    in
                                                        k (failure, TRKs)
                                                    end
                                              | tuple (* (otherTuples, ctx, domOpt, cod) *) :: rest =>
                                                    let in
                                                        Case.ff
                                                            build_pattern_tracks
                                                            (ctx, pat0, fail, A)
                                                            failure
                                                            tuple
                                                           (fn (failure, xx) =>
                                                               build failure (xx @ Xis) (tuple :: prev_tuples) rest k)
                                                    end
                                    in
                                        build failure [] [] optimizedTuples k
                                    end
                            end) (* of fn filteredTuples => ... *)
                    end (* (pat as CtorPattern (c, pat0), A) =>   case *)
        end (* build_pattern_tracks *)



    and infer_decs failure (rctx, mctx) loc pairedDecs (k : result failure * ctx * locdec list -> result) =
        let val earlyRctx = rctx   (* save rctx so we can gather the Fields(-) of the _old_ signature *)
            val (decs, pdecs) = ListPair.unzip pairedDecs
            val (locs, justDecs) = ListPair.unzip decs

            fun lookup pv  : Sdml.Dectype.dectype option =
                let
                    val getfn = lookupSorting rctx
                in
                    Option.map (Inject.inject_dectype getfn) (Sdml.getDectype pv decs)
                end
            
            val anyToplevel =
                List.exists
                  (fn ValType(_, Dectype.TOPLEVEL_AGAINST _) => true
                    | ValType(_, Dectype.TOPLEVEL_NOT _) => true
                    | _ => false)
                  justDecs
                   
            fun senseOf NONE = NONE
              | senseOf (SOME dectype) = let in case dectype of
                     Dectype.AGAINST _ => SOME true
                   | Dectype.TOPLEVEL_AGAINST _ => SOME true
                   | Dectype.TOPLEVEL_NOT _ => SOME false
                 end
            
            fun gather_type_decls failure (ctx as (rctx, mctx)) decs k =
                case decs of
                    [] => k (failure, ctx)

              | (loc, Dec(pv, kw, _)) :: decs =>
                  let val dectype = lookup pv
                  in
                     case dectype of 
                         NONE =>
                             gather_type_decls failure ctx decs k
                       
                       | SOME (Dectype.AGAINST anno) =>
                             let        
                             in
                                 check_annotation failure (rctx, mctx) loc anno
                                   (  fn (failure, mctx, A) =>
                                      (*  frameR *)
                                      (*    (mctx ++ (pv, A)) *)
                                            ((fn mctx =>
                                                 let in
                                                     gather_type_decls failure (rctx, mctx) decs
                                                 end
                                             )
                                              (mctx ++ (pv, substExtypevarNoAuto mctx A)))
                                            k  )
                             end
                       
                       | SOME (Dectype.TOPLEVEL_AGAINST texp) =>
                            (print "TOPLEVEL_AGAINST\n";
                            gather_type_decls failure (rctx, mctx ++ (pv, substExtypevarNoAuto mctx texp)) decs k)
                       
                       | SOME (Dectype.TOPLEVEL_NOT texp) =>
                            gather_type_decls failure (rctx, mctx ++ (pv, substExtypevarNoAuto mctx texp)) decs k
                  end

            | (loc, Typedec typedecs) :: decs =>
                    let val _ = dprint (fn () => "CALLING typecheck_typedecs FROM " ^ "infer_decs.gather_type_decls")
                        val ((rctx, mctx), typedecsl, elabTypedecs) = typecheck_typedecs (List.map #2 decs) (rctx, mctx) typedecs
                        val _ = dprint (fn () => "ELABORATED TYPEDECS: " ^ P.p P.printTypedecs elabTypedecs)
                                 (* NOTE: `elabTypedecs' unused except for printing; the "real" typedecs used in
                                elaboration are stored in the rctx's Typeinfo.
                                See Context.typeinfo and Context.getTypes. *)
                    in
                        gather_type_decls failure (rctx, mctx) decs k
                    end

            | (dec as (loc, TestSubtype (sense, (A, B)))) :: decs =>
                    let
                        val _ = print (P.pDec dec ^ "     ")
                        val continue = fn () =>
                                                         let in 
                                                             print "\n";
                                                             gather_type_decls failure (rctx, mctx) decs k
                                                         end

                        fun processIs (A, B) continue =
                            Subtype.subtype (fn _ => (print ("(* does not hold (incomplete?) *)");
                                                      continue()))
                                            0
                                            (rctx, mctx)
                                            A B
                                            (fn (failure, mctx', coercion) =>
                                                   let in 
                                                       print ("(* holds; coercion = " ^ Coercion.toString coercion ^ " *)");
                                                       continue()
                                                   end)

                        fun processIsNot () =
                            Subtype.subtype (fn _ => (print ("(* does not hold (OK) *)");
                                                      continue()))
                                            0
                                            (rctx, mctx)
                                            A B
                                            (fn (failure, mctx', coercion) =>
                                                   let in 
                                                       print ("(* undesired subtyping holds (UNSOUND?); coercion = " ^ Coercion.toString coercion ^ " *)");
                                                       continue()
                                                   end)
                    in
                        case sense of
                            IsSubtype => processIs (A, B) continue
                          | IsNotSubtype => processIsNot()
                          | MutualSubtypes => processIs (A, B) (fn () => processIs (B, A) continue)
                    end

            | (loc, DatatypeWith (tc, sorting)) :: decs =>
                    let fun amend1 s1 s2 = case (s1, s2) of
                           (X.Sorting.None, s2) => s2
                         | (s1, X.Sorting.None) => s1
                         | (X.Sorting.Nameless _, _) => fail ("amend1 trying to amend nameless")
                         | (_, X.Sorting.Nameless _) => fail ("amend1 trying to amend with nameless")
                         | (X.Sorting.Fields origFields, X.Sorting.Fields moreFields) =>
                             let val result =
                               X.Sorting.Fields (origFields @ moreFields)   (* XXX: check for clashes *)
                             in
                             ( PRINT ("Typecheck: amending: new sorting: " ^ X.Sorting.toString result ^ "\n")
                               ; result)
                             end

                        fun amendInfo s2 (Typeinfo{indexsort, parameters, elabTypedecs}) =
                            Typeinfo{indexsort= amend1 indexsort s2,
                                     parameters= parameters,
                                     elabTypedecs= elabTypedecs (*XXX*)}

                        val rctx = updateTypes rctx (modifyInfo tc (amendInfo sorting))
                    in
                        gather_type_decls failure (rctx, mctx) decs k
                    end

            | (loc, Datacon (pv, newType)) :: decs =>
                    gather_type_decls failure (rctx, mctx) decs k

(*
                let fun amendInfo newType (Coninfo{tc, basetype, contype,
                                                   unquant_basetype, unquant_contype,
                                                   allcons})
                                             k
                     = let val _ = PRINT ("amendInfo: " ^ PV.toShortString pv ^ "\n")
                           val params = case lookupTypeinfo rctx tc of Typeinfo {parameters, ...} => parameters
                         in
                           AG.agreesWith 
                             (fn (_, failureInfo) => raise_AllDead mctx (fn () => "[agreesWith] " ^ failureInfo()))
                             ctx
                             {oldType= unquant_contype,
                              typeToAdd= newType,
                              oldSigFields= AG.fieldsOfTypes (List.map (fn (c, _) => lookupConjuncts "amendInfo" earlyRctx c) allcons)}
                             (fn (failure, (rctx, mctx)) =>
                                let val amendedType = Sect(unquant_contype, newType)
                                    val coninfo = Coninfo {tc= tc, allcons= allcons, basetype= basetype, unquant_basetype= unquant_basetype,
                                                                       unquant_contype= amendedType,
                                                                       contype= Sdml.quantifyCtype amendedType params}
                                    val rctx = updateCon rctx (modifyInfo pv (fn _ => coninfo))
                                    val _ = PRINT ("Typecheck: Datacon: new rctx: " ^ rctxToString rctx ^ "\n")
                                in
                                    k (failure, (rctx, mctx))
                                end)
                         end
                in
                    amendInfo newType (lookupConinfo "amendInfo" rctx pv)
                      (fn (failure, ctx) => gather_type_decls failure ctx decs k)
                end
*)

            | (loc, other) :: decs =>
                 gather_type_decls failure (rctx, mctx) decs k
            (*end of fun gather_type_decls*)
            
            
            fun traverse failure ctx ([], elabDecs_acc) k = k (failure, ctx, elabDecs_acc)
            
              | traverse failure (rctx, mctx) (((loc, Dec(pv, kw, locexp)), Path.Dec pexp) :: decs, elabDecs_acc) k =
                   let in
                       case lookup pv of
                           SOME (Dectype.TOPLEVEL_NOT _) =>    (* ANTICOLON type declaration *)
                                   let val (texp, _) = lookupOrd "traverse/ANTICOLON" mctx pv
                                       val _ = PRINT ("Starting work on :!-declaration of " ^ PV.toString pv ^ "\n")
                                   in
                                       if not (Context.isSolved (rctx, mctx)) then
                                           raise_AllDead mctx (fn () => "Context not solved at start of :!-declaration.")
                                       else
                                           let
                                               val _ = PRINT ("Context solved before trying to check " ^ PV.toString pv ^ "\n")
                                               val continue = (* continue, ignoring this declaration *)
                                                         fn () =>
                                                            (PRINT (":!-declaration of " ^ PV.toString pv ^ " does not typecheck.  Continuing.\n");
                                                             traverse failure (rctx, mctx) (decs, elabDecs_acc) k
                                                            )
                                           in
                                               check (fn _ => continue()) (rctx, mctx) (locexp, pexp) texp
                                                 (fn (failureAfter, mctxAfter, elabExp) =>
                                                     if solve mctxAfter then 
                                                         raise_AllDead mctxAfter
                                                                       (fn () => ":!-declaration of " ^ PV.toString pv ^ " actually does typecheck, contrary to spec")
                                                     else
                                                         continue()
                                                 )
                                           end
                                   end

                         | SOME (_) =>    (* ordinary (COLON) type declaration *)
                                   let val (texp, _) = lookupOrd "traverse" mctx pv
                                       val _ = PRINT ("Starting work on declaration of " ^ PV.toString pv ^ "\n")
                                   in
                                       if
                                           true
                                           andalso
                                           Context.isSolved (rctx, mctx)
                                       then
                                           let
                                               val _ = PRINT ("Context solved before trying to check " ^ PV.toString pv ^ "\n")
                                           in
                                               check failure (rctx, mctx) (locexp, pexp) texp
                                                 (fn (failureAfter, mctxAfter, elabExp) =>
                                                     let 
                                                         val elabDec = Dec(pv, kw, elabExp)
                                                     in
                                                         if Context.isSolved (rctx, mctxAfter)
                                                         then
                                                             let val _ = PRINT ("Independence used for " ^ PV.toString pv ^ "\n")
                                                             in
                                                                 traverse failure(*previous failure!*) (rctx, mctx(*previous mctx!*)) (decs, elabDecs_acc @ [(loc, elabDec)]) k
                                                             end
                                                         else
                                                                 traverse failureAfter (rctx, mctxAfter) (decs, elabDecs_acc @ [(loc, elabDec)]) k
                                                     end)
                                           end
                                       else
                                           check failure (rctx, mctx) (locexp, pexp) texp
                                             ((fn (failure, mctx, elabExp) =>
                                                 let val elabDec = Dec(pv, kw, elabExp)
                                                 in
                                                     traverse failure (rctx, mctx) (decs, elabDecs_acc @ [(loc, elabDec)]) k
                                                 end))
                                   end

                       | NONE =>    (* No type annotation *)
                               let
                                   val _ = PRINT ("Trying to synthesize type of declaration of " ^ PV.toString pv ^ "\n")
                               in
                                   infer failure MAINTAIN_PRINCIPALITY (rctx, mctx) (locexp, pexp)
                                       (fn (failure, mctx, (texp, elabExp)) =>
                                          let
                                              val texp = substExtypevarNoAuto mctx texp
                                              val _ = PRINT ("Synthesized val " ^ PV.toShortString pv ^ " : " ^ t2str' mctx texp ^ "\n")
                                              val elabDec = Dec(pv, kw (* XXX *), elabExp)

                                              val mctx = mctx ++ (pv, texp)
                                          in
                                              (*
                                      frameRElab mctx (fn mctx => traverse failure (rctx, mctx) (decs, elabDecs_acc @[(loc, elabDec)])) k
                                      *)
                                              traverse failure (rctx, mctx) (decs, elabDecs_acc @[(loc, elabDec)]) k
                                          end)
                               end
                   end

              | traverse failure (rctx, mctx) (((loc, Typedec typedecs), Path.Typedec) :: decs, elabDecs_acc) k =
                    let (* val _ = print "NOT CALLING typecheck_typedecs FROM traverse\n" *)
                         (*
                        val (_, _, elabTypedecs) = typecheck_typedecs (List.map (fn ((loc, dec), path) => dec) decs) (rctx, mctx) typedecs
                   *)
                        fun scanTypedec (Datatype {tc, ...}) =
                                let
                                    val Typeinfo{elabTypedecs, ...} = lookupTypeinfo rctx tc
                                in
                                    elabTypedecs
                                end
                          | scanTypedec (Synonym {tc, ...}) = 
                                let
                                    (* Nothing to do here:
                                Stardust.silly.grm reinterprets the tc as a solved (existential) tv. *)
                                in
                                    []
                                end
                        val elabTypedecs = List.concat (List.map scanTypedec typedecs)
                        (* val _ = print "END NON-CALL of typecheck_typedecs FROM traverse\n" *)
                    in
                        traverse failure (rctx, mctx) (decs, elabDecs_acc @ [(loc, Typedec elabTypedecs)]) k 
                    end

              | traverse failure (rctx, mctx) (((loc, Datacon (c, A)), Path.Datacon) :: decs, elabDecs_acc) k =
                    traverse failure (rctx, mctx) (decs, elabDecs_acc) k 

              | traverse failure (rctx, mctx) ((_, _) :: decs, elabDecs_acc) k =
                    traverse failure (rctx, mctx) (decs, elabDecs_acc) k
(*
              | traverse ctx (Dec(SOME (Dectype.TOPLEVEL_AGAINST texp), pv, locexp) :: decs) k =
                check ctx W locexp texp (fn ctx => traverse ctx decs k)
              | traverse ctx (Dec(SOME (Dectype.TOPLEVEL_NOT texp), pv, locexp) :: decs) k =
                    check ctx W locexp texp (fn ctx => traverse ctx decs k)
*)
(*            val _ = print ("length of `justDecs' = " ^ Int.toString (List.length justDecs) ^ "\n")
            val _ = print ("`justDecs' = " ^ Print.p Print.printDecs decs ^ "\n")
*)
      in
            gather_type_decls failure (rctx, mctx) decs
              (fn (failure, (rctx', mctx')) =>
                  (if anyToplevel then
                     let (*val _ = print ("XXX "  ^ rctxToString rctx ^ "\n")*) in
                         traverse (fn stuff => raise AllDead stuff) (rctx', mctx') (pairedDecs, (*elabDecs_acc==*)[])
                                  (fn (failure, (rctx0, mctx0), elab_decs) =>
                                               let in
                                                   dprint (fn () => "\n" ^ Location.toString loc);
                                                   Counter.INC "solveCount" solveCount;
                                                   dprint (fn () => "QQQ  mctx0 =  " ^ mctxToString mctx0);
                                                   if false andalso (unsolvedExtypevars mctx0) then (*!!!!!*)
                                                                                                        ((* print "Type instantiation FAILED\n"; *) raiseDead failure mctx0 loc (fn () => "Type instantiation failed"))
                                                   else
                                                       if solve mctx0 then (adprnt "Constraint solving SUCCEEDED";
                                                                            k (failure, (rctx', mctx'), elab_decs)
                                                                           )
                                                       else (pprint (fn () => "Constraint solving FAILED");
                                                             dprint (fn () => "QQQ  mctx0 =  " ^ mctxToString mctx0);
                                                             raiseDead failure mctx0 loc (fn () => "Constraint solving failed"))
                                               end)
                     end
                 else ( (* print "not toplevel\n"; *)
                     traverse failure (rctx', mctx') (pairedDecs, []) k))
         )
      end


  fun typecheck_program (Program (libinfo, typedecsl, body as (bodyloc, bodyexp))) =
      let
          val _ = DS.printAll()

      (*    fun get_cons_typedec (Datatype (_, _, _, cons)) = map (fn Constructor{c= c, ...} => (c, ())) cons *)
      (*    fun get_cons_typedecs typedecs = List.concat (map get_cons_typedec typedecs) *)
      (*    fun get_cons_typedecsl typedecsl = List.concat (map get_cons_typedecs typedecsl) *)

         fun initialCtx (Libinfo{primtcs, primops, distinguished}) =
             let fun findInPrimops name = #1 (Option.valOf (List.find (fn (pv, _) => PV.toShortString pv = name) primops))
                 val functions = {elab_Bot = findInPrimops "elab_Bot", exit = findInPrimops "exit"}
                 val (rctx, mctx) = (Context.empty_rctx (primtcs, distinguished, functions), empty_mctx())
                 fun mkCtx ctx [] = ctx
                   | mkCtx ctx ((pv, {source_texp= texp, elaboration= elaboration, proper_name= proper_name, sanitized_name= sanitized_name}) :: rest) =
                        D.addOrdinary (pv, (texp, Primvar {elaboration= elaboration})) (mkCtx ctx rest)

                 val mctx = updateG mctx (fn G => mkCtx G primops)
             in
                 (rctx, mctx)
             end

      (* decsl, ... *)
      (*****
          fun infer_decsl ctx [] = ()
            | infer_decsl ctx (decs::decsl) = infer_decs ctx decs (fn (ctx, ctx') => infer_decsl W ctx' decsl)
      ****)

          
          val _ = Barrier.reset()
          val ctx = initialCtx libinfo
          val (ctx1, typedecsl', elabTypedecsl) = typecheck_typedecsl [] ctx (*typedecsl*) []
          
          val elabBody = check
                           (fn stuff => raise AllDead stuff)
                           ctx1
                           (body, Sdml.buildShadow (fn () => () (* ref [] (*memoization*)*)) bodyexp)
                           (Product [])
                           (fn (failure, mctx, elabBody) =>
                              let (* val fullyQuantifiedW = quantify_full (getIndex ctx) W *)
                              in
                                (*dprnt ("\n\n" ^ "CONSTRAINTS: \n" ^ X.Constraint.toString (fullyQuantifiedW) ^ "\n");
                                 *)
                                    Counter.INC "solveCount" solveCount;
                                    if solve mctx then
                                        (dprnt "Solved (index level).";
                                         Context.finalSubstLocexp mctx elabBody)
                                    else
                                        raise_Dead failure mctx (fn () => "FAILED--backtracking")
                              end)
          
          val source = Program (libinfo, [], body)
          fun define_primops [] = []
            | define_primops ((pv, {source_texp, elaboration, proper_name, sanitized_name}) :: rest) =
                  let 
                      val prelude = define_primops rest
                  in
                      ("val " ^ PV.toString pv ^ " = " ^ elaboration ^ "\n")
                      ::
                      prelude
                  end

          val prelude = case libinfo of Libinfo{primops, ...} =>
                                        String.concat (define_primops primops)
          val elaboration = Program (libinfo, [], elabBody)
          val elaboration = Destultify.destultify elaboration
      in
          {source= source,
           prelude= prelude,
           elaboration= elaboration}
      end
      handle AllDead stuff =>
                     (PRINT "Rejected toplevel declaration: short-circuiting.\n";
                      raise AllDead stuff)
  (* end fun typecheck_program *)


  fun takeLongest n [] = []
     | takeLongest n (paths as _::_) =
          let 
              fun longestLength n [] = n
                | longestLength n (p::ps) =
                        if length p > n then
                            longestLength (length p) ps
                        else
                            longestLength n ps

              val highestLength = longestLength 0 paths
          in
              case List.partition (fn p => length p = highestLength) paths of
                  (longest, shorter) =>
                         if length longest >= n then
                             List.take (longest, n)
                         else
                             longest @ (takeLongest (n - length longest) shorter)
          end
     
    fun typecheckX program =
        ( recentPaths := [];
          SOME (typecheck_program program)
          before
          PRINT "\n=== Program typechecks. ===\n\n" )
        handle AllDead (mctx, info) => ( PRINT ("\n*** Program does NOT typecheck. ***\n\n"
(*                                             ^  "*** " ^ pathToString (getPath mctx) ^"\n"
                                             ^ "*** " ^ info() ^ "\n" 
                                                            ^ "*** recent long paths:\n"
                                                            ^ Separate.list ";\n" (map pathToString (takeLongest 3 (!recentPaths))) ^ "\n" *));
                                     NONE)

  fun reset_counts () =
      (subtypeCalls := 0;
       subtypeNRCalls := 0;
       subtypeUnionSplits := 0;
       unionLeftCount := 0;
       sectLeftCount := 0;
       solveCount := 0;
       memoHit := 0;
       memoLookup := 0;
       memoAdd := 0;
       subtypeMemoHit := 0;
       subtypeMemoAdd := 0;
(*       Case.ctorPatternOrNondet := 0; *)
       caseArmChecked := 0
       )

  fun dump_counts () =
       (PRINT ("subtypeCalls, subtypeNRCalls, subtypeUnionSplits = " ^ Int.toString (!subtypeCalls) ^ ", "
               ^ Int.toString (!subtypeNRCalls) ^ ", "
               ^ Int.toString (!subtypeUnionSplits)
               ^ "\n");
(*           PRINT ("subtypeMemoAdd = " ^ Int.toString (!subtypeMemoAdd) ^ "\n");
        PRINT ("subtypeMemoHit = " ^ Int.toString (!subtypeMemoHit) ^ "\n");
*)
        PRINT ("unionLeftCount = " ^ Int.toString (!unionLeftCount) ^ "\n");
(*           PRINT ("sectLeftCount = " ^ Int.toString (!sectLeftCount) ^ "\n"); *)
        PRINT ("solveCount = " ^ Int.toString (!solveCount) ^ "\n");
(*           PRINT ("memoAdd, memoLookup, memoHit = " ^ Int.toString (!memoAdd) ^ ", "
               ^ Int.toString (!memoLookup) ^ ", "
               ^ Int.toString (!memoHit) ^ "\n"); *)
(*           PRINT ("ctorPatternOrNondet = " ^ Int.toString (!ctorPatternOrNondet) ^ "\n"); *)
        PRINT ("caseArmChecked = " ^ Int.toString (!caseArmChecked) ^ "\n")
        )

  fun typecheck program =
      (reset_counts();
       Solve.reset();
       Piper.kill_all();
(*          OS.Process.sleep (Time.fromSeconds 2); *)
       typecheckX program
       before
       (Piper.kill_all(); dump_counts()))

end
