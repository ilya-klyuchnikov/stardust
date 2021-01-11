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
(* File: Solve.sml
 * Author: Joshua Dunfield
 * Contents: Constraint solving interface, sitting between Typecheck.sml
 *           and Ics.sml / Cvcl.sml / CvclPiped.sml / Cvc4Piped.sml / Yices.sml.
 *)

signature SOLVE = sig

  datatype which = Ics | Yices | Cvcl | CvclPiped | Cvc4Piped
  val setConstraintSolver : which -> unit
  val cs : string -> unit
  val which : unit -> string

     (* "i"    ICS
      | "y"    Yices
      | "c"    CVC4 (piped)
      | "3"    CVC3 (shared library)
      | "p"    CVC3 (piped)
     *)
 
  type state
  exception SolverStartupFailed
  exception SolverFailure

  type disjuncts = Indexing.constraint list
  
  val reset : unit -> unit   (* Resets underlying constraint solving interfaces *)
  
  val empty : unit -> state
  
  val accumulate : state * Indexing.constraint -> (state * disjuncts) option   (* returns NONE if inconsistent *)
  val assume : state * Indexing.constraint -> (state * disjuncts) option   (* returns NONE if inconsistent *)
  
  val save : state -> (state * (state -> state))
  
  val ejectConstraint : state -> state * Indexing.constraint
  val unejectConstraint : state * Indexing.constraint -> state

  type point = int
  val push : state -> state * point
  val popto : state * point -> state
  
  val solve : state -> bool
  
  val getConstraint : state -> Indexing.constraint  

  val addUniversalAssn : state -> IndexSym.sym * Indexing.sort -> state option
  val addExistentialAssn : state -> IndexSym.sym * Indexing.sort -> state option

  val stateToString : state -> string

  val ok_state : state -> state   (* identity function if state satisfies certain invariants,
                                   otherwise raises an exception *)

  val knowsSym : state -> IndexSym.sym -> bool

  val forceElimExistential : state -> Indexing.constraint -> state * Indexing.constraint

  val compose : disjuncts -> disjuncts -> disjuncts   (* All combinations of djs1, djs2 *)

  val takeAlong : disjuncts -> 'a * disjuncts -> 'a * disjuncts   (* Sugared `compose' *)

  val r_earlyValidation : bool ref (* XXX *)

end (* signature SOLVE *)



structure ExiSub :> sig
      type exisub

      val empty : exisub
      val add : exisub -> IndexSym.sym * Indexing.exp -> exisub option  (* NONE if clash with current substitution *)
      val merge : exisub -> exisub -> exisub option  (* NONE if substitutions clash *)
      val toList : exisub -> (IndexSym.sym * Indexing.exp) list
      val fromList : (IndexSym.sym * Indexing.exp) list -> exisub option
      val toString : exisub -> string
end
=
struct
    open Indexing
    type exisub = (IndexSym.sym * exp) list
    
    fun isSolvedForm exisub =
        List.all (fn (sym, _) => List.all (fn (_, exp) => not (free sym exp)) exisub) exisub

    val empty = []
(*    
NEED TO ENSURE THAT EVERYTHING ADDED TO AN EXISUB IS IN COMPLETED FORM:
SHOULD NOT HAVE

iv187_d1 -> ...iv176_d...
AND
iv176_d1 -> foo,

it should be

iv187_d1 -> ...foo...
*)
    fun toList exisub = exisub

    fun toString exiSub =
        "[" ^ Separate.list ", \n" (map (fn (sym, exp) => IndexSym.toString sym ^ " -> " ^ Exp.toString exp) (toList exiSub)) ^ "]"

    fun add exisub (sym, exp) =
        let val _ = if not (isSolvedForm exisub) then raise Div else ()
            val exp = Indexing.subst exisub exp
(*            val _ = print ("@@@@/  " ^ toString (exisub) ^ "\n\n") *)
        in
            case List.find (fn (sym', _) => sym=sym') exisub of
                NONE =>
                    let fun substituteNew (sym', exp') =
                          (sym', Indexing.subst [(sym, exp)] exp')
                        val exisub = List.map substituteNew exisub
(*                        val _ = print ("@@@@@. " ^ toString ((sym, exp) :: exisub) ^ "\n") *)
                        val _ = if not (isSolvedForm ((sym, exp) :: exisub)) then raise Div else ()
                    in
                        SOME ((sym, exp) :: exisub)
                    end
              | SOME (sym', exp') =>
                    let fun substituteNew (sym', exp') =
                          (sym', Indexing.subst [(sym, exp)] exp')
                        val exisub = List.filter (fn (sym',_) => sym<>sym') exisub
                        val exisub = List.map substituteNew exisub
                        val result = ((sym, exp) :: exisub)
(*                        val _ = print ("@@@@@! " ^ toString result ^ "\n") *)
                        val _ = if not (isSolvedForm result) then raise Div else ()
                    in
                        SOME result
                    end                    
(*                    if exp = exp' then
                        SOME exisub
                    else
                        (print ("ExiSub.add clash: " ^ IndexSym.toString sym ^ "\n"
                               ^ "   -> " ^ Exp.toString exp ^" \n"
                               ^ " but also \n"
                               ^ "   -> " ^ Exp.toString exp' ^ " \n");
                        NONE)
*)
        end
    
    fun merge [] exisub2 = SOME exisub2
      | merge ((sym, exp) :: exisub1) exisub2 =
          case merge exisub1 exisub2 of
              NONE => NONE
            | SOME result => add result (sym, exp)
     
    fun fromList [] = SOME empty
      | fromList ((sym, exp)::rest) =
        let in case fromList rest of
            NONE => NONE
          | SOME exiSub => add exiSub (sym, exp)
        end
end (* structure ExiSub *)



functor SolveFn (structure U : SOLVER_INTERFACE) = struct

  fun frame s f x =
      ( (* print ("# frame {   " ^ s() ^ "\n"); *)
       f x (*
       before
       print ("# frame }  "  ^ s() ^ "\n") *))

  open Indexing

  structure IV = IndexSym
  structure IS = IndexSortSym

  val r_earlyValidation = ref true

  val {dprint, dprnt} =
          Debug.register {full_name= "Solve",
                          short_name= "Solve"}

  datatype indexassn =
      Iall of IV.sym * sort
    | Iexists of IV.sym * sort
    | Iprop of constraint

  val EStoList = ExiSub.toList

  type point = U.point
  datatype state = STATE of {
                             assn : indexassn list,
                             constraint : constraint,
                             exiSub : ExiSub.exisub,
                             context : U.context
                             }
  exception SolverFailure
  exception SolverStartupFailed

  fun getAssn (STATE{assn=assn, ...}) = assn
  fun setExiSub (STATE{assn=assn,constraint=constraint,exiSub=exiSub,context=context}) exiSub' =
      STATE{assn=assn, constraint=constraint, exiSub=exiSub', context=context}

  fun lookupUvar [] sym = NONE
    | lookupUvar (Iall(a, sort) :: rest) sym = if a=sym then SOME sort else lookupUvar rest sym
    | lookupUvar (_ :: rest) sym = lookupUvar rest sym

  fun lookupEvar [] sym = NONE
    | lookupEvar (Iexists(a, sort) :: rest) sym = if a=sym then SOME sort else lookupEvar rest sym
    | lookupEvar (_ :: rest) sym = lookupEvar rest sym

  fun indexassnToString (Iall (sym, sort)) = "ALL " ^ IV.toString sym
    | indexassnToString (Iexists (sym, sort)) = "EXI " ^ IV.toString sym
    | indexassnToString (Iprop P) = "P[" ^ Constraint.toString P ^ "]"

  fun assnToString assn = Separate.list ", " (map indexassnToString assn)

  fun exiSubToString exiSub = ExiSub.toString exiSub

  fun stateToString (STATE{assn, constraint, exiSub, context}) =
      "STATE{"
      ^ "assn= " ^ assnToString assn
      ^ ", constraint= " ^ Constraint.toString constraint
      ^ ", exiSub= " ^ exiSubToString exiSub
     ^ ", context= " ^ U.glork context
      ^ "}"
  
  fun domain assn =
      let fun f (Iall (a, _)) = SOME a
            | f (Iexists (a, _)) = SOME a
            | f (Iprop _) = NONE
      in
          List.mapPartial f assn
      end

  fun ok_state (state as STATE{assn, constraint, exiSub, context}) =
      let fun ok_constraint boundvars W =
          let fun ok_exp exps =
              let val bogusVars = List.concat (map (freeVars boundvars) exps)
              in
                  case bogusVars of
                      [] => ()
                    | bogusVars => (print ("Solve.sml: ok_state: ok_constraint: "
                                           ^ "unbound variables: " ^ Separate.list ", " (map (IV.toString) bogusVars)
                                           ^ "\n");
                                    raise Option)
              end
              fun failTwiceBound a =
                  (print ("Solve.sml: ok_state: ok_constraint:"
                          ^ "\n  twice-bound variable: " ^ IV.toString a
                          ^ "\n assumptions: " ^ assnToString assn
                          ^ "\n  in constraint: "
                          ^ "\n  " ^ Constraint.toString constraint
                          ^ "\n");
                   raise Option)
          in
          case W of
              TRUE => ()
            | AND(W1, W2) => (ok_constraint boundvars W1; ok_constraint boundvars W2)
            | OR(W1, W2) => (ok_constraint boundvars W1; ok_constraint boundvars W2)
            | IMPLIES(W1, W2) =>  (ok_constraint boundvars W1; ok_constraint boundvars W2)
            | ALL(a, sort, W0) =>
                if MyList.contains a boundvars then
                    failTwiceBound a
                else
                    ok_constraint (a :: boundvars) W0
            | EXISTS(a, sort, W0) =>
                if MyList.contains a boundvars then
                    failTwiceBound a
                else
                    ok_constraint (a :: boundvars) W0
            | PRED(sym, exp) => ok_exp [exp]
            | EQ(_, e1, e2) => ok_exp [e1, e2]
          end
      in
          (ok_constraint (domain assn) constraint;
           state)
      end
 
  val okSTATE = ok_state o STATE

  fun knowsSym (STATE{context, ...}) a =
    U.knowsSym context a
  
  fun update_constraint (STATE{constraint, assn, exiSub, context}) f =
      ok_state (STATE{constraint=f constraint, assn=assn, exiSub=exiSub, context=context})
  fun update_assn (STATE{constraint, assn, exiSub, context}) f =
      ok_state (STATE{constraint=constraint, assn=f assn, exiSub=exiSub, context=context})
  fun update_exiSub (STATE{constraint, assn, exiSub, context}) f =
      ok_state (STATE{constraint=constraint, assn=assn, exiSub=f exiSub, context=context})
  fun update_context (STATE{constraint, assn, exiSub, context}) f =
      ok_state (STATE{constraint=constraint, assn=assn, exiSub=exiSub, context=f context})

  fun updateConstraint (STATE{constraint, assn, exiSub, context}) constraint' =
      ok_state (STATE{constraint=constraint', assn=assn, exiSub=exiSub, context=context})

  datatype assertresult =
      Unsat
    | Okay of state
    | Valid
  
  fun empty () = ( (*raise SolverStartupFailed; *)
      okSTATE{constraint= TRUE,
            assn= [],
            exiSub= ExiSub.empty,
            context= case U.Context.new (U.getLocation ()) of
                       NONE => raise SolverStartupFailed
                     | SOME context => context
            })

  fun addAssumption (S as STATE{context= context, assn= assn, ...}) c (a, sort) =
      if List.exists (fn Iall(a', _) => a' = a
                       | Iexists(a', _) => a' = a
                       | _ => false) assn then   (* Variable already in assumptions! *)
            (print ("Solve.addAssumption: variable " ^ IV.toString a ^ " already in assumptions\n");
             raise Option)
      else
          let val S = update_assn S (fn assn => c(a, sort) :: assn)
          in
              case
                  (dprint (fn () => "UDS-1: " ^ IndexSym.toString a);
                   U.declare) (context, (a, sort))
               of
                  U.Valid => SOME S
                | U.Ok(context, _) => SOME (update_context S (fn _ => context))
                | U.Unsat => NONE (* 2013-01-24; was `raise Option' *)
          end

  fun addUniversalAssn S (a, sort) =      
      addAssumption S Iall (a, sort)

  fun addExistentialAssn S (a, sort) =   
      addAssumption S Iexists (a, sort)

  fun findCandidates exvar W =
            case W of
                TRUE => []
              | AND(W1, W2) => findCandidates exvar W1 @ findCandidates exvar W2
              | OR(W1, W2) => []   (* XXX *)
              | PRED _ => []
              | ALL(_, _, W0) => findCandidates exvar W0
              | EXISTS(_, _, W0) => findCandidates exvar W0
              | EQ(_, Evar v1, e2) =>
                    if v1=exvar andalso not (free exvar e2)  then [e2]
                    else
                        let in case e2 of
                            Evar v2 => if v2=exvar andalso v1 <> v2 then  [Evar v1] else []
                          | _ => []
                        end
              | EQ(_, e1, Evar v2) => 
                    if v2=exvar andalso not (free exvar e1) then [e1] else []
              | EQ(_, _, _) => []
              | IMPLIES(_, _) => []

  fun existential assns a = List.exists (fn assn =>
                                        case assn of Iexists(a', sort) => a=a'
                                      | Iall _ => false
                                      | Iprop _ => false) assns

  fun supplement assn exiSub eqs =
      case eqs of 
          [] => (dprint (fn () => "length(assn) = " ^ Int.toString (length assn) ); exiSub)
        | (aexp, exp) :: eqs => 
              let val rest = supplement assn exiSub eqs
              in
                      case aexp of
                          Evar a =>
                              valOf (ExiSub.add rest (a, exp))
                        | Uvar a => 
                              let in case exp of
                                  Evar b => valOf (ExiSub.add rest (b, Uvar a)) (* XXXZZZ *)
                                | _ =>
                                      if free a exp then rest
                                      else rest   (* [(a, exp)] @ rest   Should never subst. for universal variables! *)
                              end
                        | _ => rest
              end
(*          if existential assn a then (dprnt "WHOOP\n"; (a, exp) :: rest)
               else let in case exp of
                   Evar v2 =>  (dprnt "WHOOPI\n"; (v2, Evar a) :: rest)
                 | _ => rest
                    end
*)

  fun supplementS (STATE{assn, constraint, exiSub, context}) eqns =
      STATE{assn= assn, constraint= constraint, exiSub= supplement assn exiSub eqns, context= context}

  fun varMaker (assn, W) sym =
      let fun isExistential sym W =
          case W of
              TRUE => false
            | AND(W1, W2) => isExistential sym W1 orelse isExistential sym W2
            | OR(W1, W2) => isExistential sym W1 orelse isExistential sym W2
            | ALL(a, sort, W0) => if a=sym then false else isExistential sym W0
            | EXISTS(a, sort, W0) => if a=sym then true else isExistential sym W0
            | EQ _ => false
            | IMPLIES(W1, W2) => isExistential sym W1 orelse isExistential sym W2
            | PRED _ => false

          val c =
              if existential assn sym orelse isExistential sym W then
                  Evar
              else
                  Uvar
      in
          c sym
      end

(*
  fun allBases exp =
      case exp of
          NODIM => []
        | BaseDim b => b
        | Uvar sym => sym
        | Evar sym => sym (* ??? *)
        | App(sym, exp) =>
            if sym = lookupFun "^" then
                case exp of Tuple[base, expo] => allBases base
            else
                allBases exp
        | Tuple exps => List.concat (map allBases exps)
        | _ => false

  fun ambit a W = 
      case W of
          TRUE => []
        | AND(W1, W2) => ambit a W1 @ ambit a W2
        | OR(W1, W2) => ambit a W1 @ ambit a W2
        | IMPLIES(W1, W2) => ambit a W1 @ ambit a W2
        | ALL(a, sort, W0) => ambit a W0
        | EXISTS(a, sort, W0) => ambit a W0
        | PRED(sym, exp) => []
        | EQ(sort, e1, e2) =>
             if (sort = Base(getDimSort())) andalso (free a e1 orelse free a e2) then
                 MyList.elimDups (allBases e1 @ allBases e2)
             else
                 []
*)
  fun dimlate ambitry W =
      case W of
          TRUE => TRUE
        | AND(W1, W2) => AND(dimlate ambitry W1, dimlate ambitry W2)
        | OR(W1, W2) => OR(dimlate ambitry W1, dimlate ambitry W2)
        | IMPLIES(W1, W2) => IMPLIES(dimlate ambitry W1, dimlate ambitry W2)
        | ALL(a, sort, W0) =>
            if sort = Base(getDimSort()) then
(*                let val ambit = ambit a W0
                    val ambit = List.filter (fn sym => sym <> a) ambit
                    val children = List.map (fn ambitter => (ambitter, IV.fresh (IV.toShortString a ^ "_" ^ IV.toShortString ambitter))) ambit
                    val ambitry = (a, children) :: ambitry
                in
                    List.foldr (fn ((_, child), W0) => ALL(child, sort, W0)) (dimlate ambitry W0) ambit
                end
*) dimlate ambitry W0
            else
                ALL(a, sort, dimlate ambitry W0)
        | EXISTS(a, sort, W0) => EXISTS(a, sort, dimlate ambitry W0)
        | PRED(sym, exp) => PRED(sym, exp)
        | EQ(sort, e1, e2) =>
            if sort <> Base (getDimSort()) then
                EQ(sort, e1, e2)
            else
                case e1 of
                    NODIM =>
                      let fun zeroEquals exp = EQ(Base (getIntSort()), Literal(getIntSort(), "0"), exp) 
                          fun f exp = case exp of
                                          NODIM => TRUE
                                        | BaseDim b => zeroEquals (Literal(getIntSort(), "1"))
                                        | App(sym, exp) =>
                                            if sym = lookupFun "^" then
                                                case exp of Tuple[base, expo] => zeroEquals expo
                                            else
                                                f exp
                                        | Tuple[exp1, exp2] => mkAND(f exp1, f exp2)
                      in
                          f e2
                      end
                  | _ => raise Option

(*--------------------------------------------------------------------*)
(*  Boolean sort *)
(*--------------------------------------------------------------------*)
  fun inferSort assn exp =
       let val infer = inferSort assn
           fun fail s = (print ("Solve's inferSort failed: " ^ s ^ "\n"); raise Option)
       in
         case exp of
             Uvar a =>
                 valOf (lookupUvar assn a)
           | Evar a =>
                 valOf (lookupEvar assn a)
           | Nil a =>
                 let in case getSyminfo a of
                     SOME (INil sort) => sort
                 end
           | NODIM => Base (getDimSort() )
           | BaseDim _ => Base (getDimSort() )

           | True => Base (getBoolSort() )
           | False => Base (getBoolSort() )

           | Literal(basesortname, _) => Base basesortname
           | App(fsym, exp) => 
                 let in case getSyminfo fsym of
                     SOME (IFun components) =>
                     (* Index functions have a very poor excuse for intersection sorts:
                      I don't expect this to work properly unless the components of the
                      pseudo-intersection have disjoint domains, because there is no backtracking.
                      *)
                     let fun try {domain, range, complement} =
                             subsort (domain, infer exp)
                     in
                         case List.find try components of
                             NONE => fail "---"
                           | SOME {range= range, ...} => range
                     end
                   | NONE => fail ("unknown symbol ``" ^ IndexSym.toShortString fsym ^ "''")
                   | sort => fail ("``" ^ IndexSym.toShortString fsym ^ "'' is not an index function")
                 end
           | Tuple exps => Product (map infer exps)
           | Proj(n, exp) =>
                 let in case infer exp of
                     sort as Product sorts =>
                         let in 
                             (List.nth (sorts, n - 1))
                             handle Subscript =>
                                 fail ("projection #" ^ Int.toString n ^" applied to object of sort " ^ Sort.toString sort)
                         end
                   | sort => fail ("projection applied to object of sort " ^ Sort.toString sort)
                 end
       end

     fun constraintize assn e =
         let val r = case e of
                        App(p, arg) =>
                         let in case (arg, (p = lookupFun "=")) of
                                    (Tuple[e1, e2], true) => debooleanate assn (EQ(inferSort assn e1, e1, e2)) (*PRED(p, arg)*) (* EQ(___, e1, e2) *)
                                  | (arg, _) => PRED(p, arg)
                         end
                      | Evar evar => TRUE (* !! XXX *)
                      | Uvar uvar => TRUE (* !! XXX *)
                      | Nil sym => raise Option
                      | True => TRUE
                      | False => raise Option
                      | Literal _ => raise Option
                      | Tuple _ => raise Option
                      | Proj _ => raise Option
         in
(*             print ("constraintize(" ^ Exp.toString e ^ ") = " ^ Constraint.toString r ^ "\n"); *)
             r
         end

     and negate_constraintize assn e =
         case constraintize assn e of
             PRED(p, arg) => PRED(complementOf p, arg)
           | TRUE => TRUE
           | EQ(sort, e1, e2) => PRED(lookupFun "<>", Tuple[e1, e2])

     and debooleanateEQ assn (e1, e2) =
         case (e1, e2) of
             (True, e2) =>  (* TRUE = e2     <===>    e2 *)
                 constraintize assn e2
           | (False, e2) => (* FALSE = e2   <===>  not e2 *)
                 negate_constraintize assn e2
           | (e1, True) => (* e1 = TRUE   <===>    e1 *)
let val result =
                 constraintize assn e1
in 
  print ("debooleanate (" ^ Exp.toString e1 ^ ", " ^ Exp.toString e2 ^ " ) returning " ^ Constraint.toString result ^ "\n");
  result
end
           | (e1, False) =>  (* e1 = FALSE   <===>  not e1 *)
                 negate_constraintize assn e1
           (*                                 let val int = getIntSort()
                                 in 
                                     EQ(Base int, Literal(int, "0"), Literal(int, "1"))
                       end
                   *)
           | (e1, e2) => let val W1 = constraintize assn e1
                             val W2 = constraintize assn e2
(*                             val _ = print "A large ax comes your way...\n" *)
                         in 
                             mkAND(mkIMPLIES(W1, W2),
                                     mkIMPLIES(W2, W1))
                         end

   and debooleanate assn W =
       if U.canHandleBooleans then W
       else
           let in case W of
                      TRUE => TRUE
                    | AND(W1, W2) => AND(debooleanate assn W1, debooleanate assn W2)
                    | OR(W1, W2) => OR(debooleanate assn W1, debooleanate assn W2)
                    | IMPLIES(W1, W2) => IMPLIES(debooleanate assn W1, debooleanate assn W2)
                    | ALL(a, sort, W0) =>
                        ALL(a, sort, debooleanate (Iall(a, sort) :: assn) W0)
                    | EXISTS(a, sort, W0) =>
                        EXISTS(a, sort, debooleanate (Iall(a, sort) :: assn) W0)
                    | PRED(sym, exp) => PRED(sym, exp)
                    | EQ(sort, e1, e2) =>
                        if sort <> Base (getBoolSort()) then
                            EQ(sort, e1, e2)
                        else
                            debooleanateEQ assn (e1, e2)
           end

(*--------------------------------------------------------------------*)
(* assert' *)
(*--------------------------------------------------------------------*)

  fun assert' addToConstraint (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context}) Wnew =
      let val sWnew = Constraint.subst (EStoList exiSub) Wnew
          val sWnew = dimlate [] sWnew
          val sWnew = debooleanate assn sWnew
      in
          case U.assert (context, sWnew, varMaker (assn, W)) of

              (U.Unsat, []) => (Unsat, [])

            | (U.Ok (context', eqs), djs) =>
                  let val exiSub' = supplement assn exiSub eqs
                  in
                     (Okay(frame (fn () => "assert'")
                                 okSTATE
                                    {assn= if addToConstraint then assn else (Iprop Wnew) :: assn,
                                     constraint= if addToConstraint then mkAND(W, Wnew) else W,
                                     exiSub= exiSub',
                                     context= context'}),
                      djs)
                 end

            | (U.Valid, djs) =>
                 (if addToConstraint then (* Valid *)
                      Okay(  okSTATE {assn= assn,
                                      constraint= mkAND(W, Wnew),
                                      exiSub= exiSub,
                                      context= context} )
                  else Okay( okSTATE {assn= (Iprop Wnew) :: assn,
                           constraint= W,
                           exiSub= exiSub,
                           context= context}),
                 djs)

            | _ => raise Match
      end

(*
 and assert addToConstraint (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context}) Wnew = Valid
*)
(*

subtypeCalls = 41433
subtypeNZCalls = 5456
subtypeNRCalls = 5456
subtypeUnionSplits = 0
unionLeftCount = 0
solveCount = 4
memoAdd = 1583
memoHit = 2655
ctorPatternOrNondet = 1372
caseArmChecked = 1003
MEAN OF: [[[
   Typecheck: 18.850 / wall 40.492
]]]
Typecheck: 14.290 / wall 30.800

*)
 and assert addToConstraint (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context}) Wnew =
     let val _ = dprint (fn () => "assert " ^ Bool.toString addToConstraint ^ " " ^ stateToString S ^ "\n  Wnew =  " ^ Constraint.toString Wnew ^ " ...\n")
         val (result, djs) = assert' addToConstraint S Wnew
         val _ = dprint (fn () => "result = " ^ (case result of 
             Unsat => "Unsat"
           | Okay(STATE{constraint, ...}) => Constraint.toString constraint
           | Valid => "Valid"
                            ) ^ "\n")
     in
         (result, djs)
     end


  fun noExistentials (S as STATE{assn= assn, constraint= constraint, exiSub= exiSub, context= context}) W =
      let val universals = List.mapPartial (fn assn => case assn of Iall(a, sort) => SOME a  | _ => NONE) assn
      in
          case Constraint.freeVars universals W of
              [] => true
            | _ :: _ => false
      end

  fun collectExistentials (S as STATE{assn= assn, constraint= constraint, exiSub= exiSub, context= context}) W =
      let val universals = List.mapPartial (fn assn => case assn of Iall(a, sort) => SOME a  | _ => NONE) assn
      in
          Constraint.freeVars universals W
      end

  fun normalizeDimensionEQ eliminate assn (d1, d2) =
   (* Normalize the dimension equation d1 = d2 to NODIM = d1^-1 * d2,
    collecting all like bases together and ordering them as follows:
    
    var1^x1 * ... * varM^xM * B1^y1 * ... * BN^yN
    
    where var1, ..., varM are index variables and B1, ..., BN are base sorts
    (BaseDim _'s such as `M' and `S').
    
    Also solve for the first existential encountered, producing a (sym, exp) pair.
    *)
      let 
(*          val _ = print ("\nnormalizeDimensionEQ " ^ Bool.toString eliminate ^ " " ^ Exp.toString d1 ^ "    =    " ^ Exp.toString d2 ^ " \n\n") *)
          val int = getIntSort()
          val dim = Base (getDimSort())
          val [plus, minus, times, slash, pow] = List.map lookupFun ["+", "-", "*", "/", "^"]
          val one = Literal(int, "1")
          val minusOne = Literal(int, "~1")
          fun mkPow (d1, d2) =
              App(pow, Tuple[d1, d2])
          fun mkInverse d = mkPow (d, minusOne)
          fun mkProduct (d1, d2) =
              App(times, Tuple[d1, d2])
          fun mkProduct (Literal(sort, string1), Literal(_, string2)) =
                Literal(sort, Int.toString (valOf (Int.fromString string1) * valOf (Int.fromString string2)))
            | mkProduct (Literal(sort, "1"), d) = d
            | mkProduct (d, Literal(sort, "1")) = d
            | mkProduct (d1, NODIM) = d1
            | mkProduct (NODIM, d2) = d2
            | mkProduct (d1 as Literal(sort1, "~1"), d2 as App(sym, Tuple[Literal(sort2, "~1"), d3])) =
                if sym = times then
                    d3
                else
                    App(times, Tuple[d1, d2])
            | mkProduct (d1, d2) = App(times, Tuple[d1, d2])
          fun mkSlash (Literal(sort, "~1"), Literal(_, "~1")) = Literal(sort, "1")
            | mkSlash  (Literal(sort, "1"), Literal(_, "~1")) = Literal(sort, "~1")
            | mkSlash  (d, Literal(_, "1")) = d
            | mkSlash  (d, Literal(sort, "~1")) = mkProduct(Literal(sort, "~1"), d)
            | mkSlash  (d1, d2) = App(slash, Tuple[d1, d2])
          fun mkPlus (Literal(sort, string1), Literal(_, string2)) =
                Literal(sort, Int.toString (valOf (Int.fromString string1) + valOf (Int.fromString string2)))
            | mkPlus (d1, d2 as App(sym, Tuple[d21 as Literal(sort, "0"), d22])) =
                if sym = minus then
                    App(minus, Tuple[d1, d22])
                else
                    App(plus, Tuple[d1, d2])
            | mkPlus (d1, d2) = App(plus, Tuple[d1, d2])

          fun isExistential sym =
              List.exists (fn assn =>
                           case assn of
                               Iexists(sym', _) => sym'=sym
                             | _ => false)
                assn
          
          (* distributePowers : exp -> exp -> (exp * exp) list *)
          fun distributePowers n d =   (* Also turns / into * *)
             let
(*                val _ = print ("distributePowers " ^ Exp.toString n ^ "  over  " ^ Exp.toString d ^ "\n") *)
                val result = 
              case d of
                  App(sym, Tuple[d1, d2]) =>
                      if sym = times then
                          (distributePowers n d1) @ (distributePowers n d2)
                      else if sym = pow then
                          distributePowers (mkProduct (n, d2)) d1
                      else if sym = slash then
                          (dprint (fn () => "sym=slash; " ^ Exp.toString d1 ^ "   /   " ^ Exp.toString d2 ^ "\n");
                          distributePowers n (App(times, Tuple[d1, mkInverse d2])))
                      else
                          (print ("Can't distribute power over index expression containing `" ^ IndexSym.toShortString sym ^ "'\n");
                           print ("(Ill-sorted index expression?)\n");
                           raise Option)
                | Literal _ => raise Option (* " *)
                | NODIM => []
                | other => [(other, n)]
             in
(*               print (Separate.comma (map (fn (base, exponent) => "  " ^ Exp.toString base ^ " ^ " ^ Exp.toString exponent) result) ^ ".\n"); *)
                 result
             end

          fun collectLikeBases [] = []
            | collectLikeBases (all as ((base, exponent) :: rest)) =
              let val (like, unlike) = List.partition (fn (base', exponent') => base' = base) rest
                  val sum = List.foldr mkPlus exponent (List.map #2 like)
              in
                  (base, sum) :: collectLikeBases unlike
              end
          
          val factorSeq = distributePowers one (mkProduct(mkInverse d1, d2))
          val collectedFactorsSeq = collectLikeBases factorSeq

          val _ = dprint (fn () => "***collectedFactorsSeq  "
                         ^ Separate.list "   *   " (List.map (fn (base, exponent) => Exp.toString base ^ " ^ " ^ Exp.toString exponent) collectedFactorsSeq))

          val existentialFactor  = if eliminate then List.find (fn (base, exponent) =>
                                                case base of
                                                    Evar sym => isExistential sym
                                                  | Uvar sym => isExistential sym
                                                  | _ => false) collectedFactorsSeq
                                   else NONE

(*          base^exponent * d = NODIM
--->   base^exponent = d^-1
--->   base^exponent = d^(-1/exponent)
 *)
          val existentialSolution = 
              case existentialFactor of
                  NONE => NONE
                | SOME (exisBase as Evar sym, exisExponent) =>
                    SOME (sym,
                     #1 (normalizeDimensionEQ false assn
                         (NODIM,
                          List.foldr (fn ((base, exponent), rest) =>
                                         let val newExponent = mkProduct(minusOne, mkSlash (exponent, exisExponent))
                                         in
                                             mkProduct(mkPow (base, newExponent), rest)
                                         end)
                                     NODIM
                                     (List.filter (fn (base, _) => base <> exisBase) collectedFactorsSeq))))

          val _ = case existentialSolution of
                      NONE => ()
                    | SOME (sym, exp) => dprint (fn () => "OBTAINED solution for: " ^ Exp.toString (Evar sym)
                                                ^ "   |-->  " ^ Exp.toString exp ^ "\n")

          val d' =
              List.foldr
                (fn ((base, exponent), rest) => mkProduct(mkPow (base, exponent), rest))
                NODIM
                collectedFactorsSeq
      in
           (d',  existentialSolution)
      end

  fun normalize assn (subst : ExiSub.exisub) (W : constraint) =
      let fun isDimSort sort = (sort = Base(getDimSort()))

          fun isDimVar sym =
              List.exists (fn assn =>
                           case assn of
                               Iall(sym', sort') => sym'=sym andalso isDimSort sort'
                             | Iexists(sym', sort') => sym'=sym andalso isDimSort sort')
                assn

          fun isDim exp = case exp of
          NODIM => true
        | BaseDim _ => true
        | Uvar sym => isDimVar sym
        | Evar sym => isDimVar sym

        | Nil _  => false
        | True => false
        | False => false
        | Literal _ => false
        | App(sym, exp) => isDim exp
        | Tuple exps => if (not (List.all (not o isDim) exps) andalso not (List.all isDim exps)) then raise Option (* dammit *)
                        else (List.all isDim exps)
        | Proj(_, exp) => isDim exp

          fun norm assn subst W k = k (normalize assn subst W)
      in
          case W of
              TRUE => (TRUE, subst)
            | PRED(sym, exp) => (PRED(sym, exp), subst)
            | AND(W1, W2) => norm assn subst W1 (fn (W1, subst) =>
                                                    norm assn subst W2 (fn (W2, subst) =>
                                                                           (AND(W1, W2), subst)))
            | OR(W1, W2) => norm assn subst W1 (fn (W1, subst) =>
                                                    norm assn subst W2 (fn (W2, subst) =>
                                                                           (OR(W1, W2), subst)))
            | IMPLIES(W1, W2) => norm assn subst W1 (fn (W1, subst) =>
                                                    norm assn subst W2 (fn (W2, subst) =>
                                                                           (IMPLIES(W1, W2), subst)))
            | ALL(sym, sort, W) => norm (Iall(sym, sort) :: assn) subst W (fn (W, subst) =>
                                                                              (ALL(sym, sort, W), subst))
            | EXISTS(sym, sort, W) => norm (Iall(sym, sort) :: assn) subst W (fn (W, subst) =>
                                                                              (EXISTS(sym, sort, W), subst))
            | EQ(sort, i1, i2) =>
                  if not (isDimSort sort) then (EQ(sort, i1, i2), subst)
                  else let val S = Indexing.subst (EStoList subst)
                           val (rhs, sol : (sym * exp) option) = normalizeDimensionEQ true assn (S i1, S i2)
                           val eqn = EQ(sort, NODIM, rhs)
                       in
                           case sol of
                               NONE =>
                                  let val _ = dprint (fn () => "****** Ended up with eqn:  " ^ Constraint.toString eqn ^ "\n")
                                  in (eqn, subst) end
                             | SOME pair => (TRUE, valOf (ExiSub.add subst pair))
                       end
      end

  fun assume (S as STATE{assn= assn, exiSub= exiSub, ...}, newAssumption) =
      let val (newAssumption, exiSub') = normalize assn exiSub newAssumption
          val S = setExiSub S exiSub'
          val assn = () and exiSub = ()
      in
          case assert false S newAssumption of
              (Unsat, []) => NONE
            | (Valid, djs) => SOME (S, djs)
            | (Okay newS, djs) => SOME (newS, djs)
      end

  fun checkOK s =
      let val dom = List.map (#1) s
          val ok = List.all (fn (_, e) => List.all (fn x => not (free x e)) dom) s
      in
          if ok then ()
          else (dprint (fn () =>
                           Separate.list ",\n" (List.map (fn (x,e) => IndexSym.toString x ^ " |-> " ^ Exp.toString e) s)  );
                raise Option)
      end      

  fun applyToSelf [] = []
    | applyToSelf ((a, e) :: s) =
        (a, subst s e) :: applyToSelf s
  val applyToSelf = List.rev o applyToSelf o List.rev

  fun spin n f W =
      let val W1 = f W
      in
          if (n <= 0) orelse (W = W1) then W
          else spin (n - 1) f W1
      end

  fun solve (exvar, e1, e2) =
      let val [plusFun, minusFun, timesFun, divFun] = List.map lookupFun ["+", "-", "*", "/"]
          val natSort = getIntSort()
          fun mkLit n = Literal (natSort, Int.toString n)
          fun solve v e1 e2 =  (* v free in e1 *)
              let in case (e1, e2) of
                  (Evar v1, e2) => if v=v1 then e2 else raise Option (* invariant:  free v e1  violated *)
                | (App(f, Tuple[u1,u2]), e2) =>
                      (if f = plusFun then
                           (if free v u1 then   (* u1 + u2 = e2  --->  u1 = e2 - u2 *)
                                solve v u1 (App(minusFun, Tuple[e2, u2]))
                            else (* u1 + u2 = e2  --->  u2 = e2 - u1 *)
                                solve v u2 (App(minusFun, Tuple[e2, u1])))
                       else if f = minusFun then
                           (if free v u1 then   (* u1 - u2 = e2  --->  u1 = e2 + u2 *)
                                solve v u1 (App(plusFun, Tuple[e2, u2]))
                            else  (* u1 - u2 = e2  --->  -u2 = e2 - u1
                                   --->   u2 = 0 - (e2 - u1)  *)
                                solve v u2 (App(minusFun, Tuple[mkLit 0,
                                                                App(minusFun, Tuple[e2, u1])])))
                            else if f = timesFun then
                                (if free v u1 then    (* u1 * u2 = e2   ---->   u1 = 1/u2 * e2 *)
                                     solve v u1 (App(timesFun, Tuple[App(divFun, Tuple[mkLit 1, u2]),
                                                                     e2]))
                                 else  (* u1 * u2 = e2   ----> u2 = 1/u1 * e2 *)
                                     solve v u2 (App(timesFun, Tuple[App(divFun, Tuple[mkLit 1, u1]),
                                                                     e2])))
                            else Evar v (* too inept to handle `/' *))
                | (Tuple (e1 :: e1s), Tuple (e2 :: e2s)) =>
                      if free v e1 then solve v e1 e2
                      else solve v (Tuple e1s) (Tuple e2s)
                | _ => raise Option
              end
      in
          let val r = solve exvar e1 e2
          in
              if free exvar r then Evar exvar
              else r
          end
      end

  fun eliminate' attempt a s W k =
      case W of
          TRUE => k (s, W)
        | AND(W1, W2) =>
              eliminate' attempt a s W1
                (fn (s, W1) => eliminate' attempt a s W2
                   (fn (s, W2) => k (s, mkAND(W1, W2))))
        | OR(W1, W2) =>
              eliminate' attempt a s W1
                (fn (s, W1) => eliminate' attempt a s W2
                   (fn (s, W2) => k (s, mkOR(W1, W2))))
        | IMPLIES(W1, W2) => 
              eliminate' attempt a s W1
                (fn (s, W1) => eliminate' attempt a s W2
                   (fn (s, W2) => k (s, mkIMPLIES(W1, W2))))
        | ALL(b, sort, W0) =>
              eliminate' attempt a s W0
                (fn (s, W0) => k (s, ALL(b, sort, W0)))
        | EXISTS(b, sort, W0) => 
              eliminate' attempt b s W0
              (fn (s, W0) =>
               if List.exists (fn (b',_) => b=b') s then
                   eliminate' attempt a s W0 k
               else
                   eliminate' attempt a s W0 (fn (s, W0) => k (s, EXISTS(b, sort, W0))))
        | PRED(pred, e) => k (s, PRED(pred, subst s e))
        | EQ(sort, e1, e2) =>
              let val e1 = subst s e1
                  val e2 = subst s e2
                  val r = if free a e1 andalso not (free a e2) then
                      solve (a, e1, e2)
                          else if free a e2 andalso not (free a e1) then
                              solve (a, e2, e1)
                               else Evar a
(*                                   val _ = dprnt ("@@ " ^ Exp.toString r ) *)
              in
                  if r = Evar a then
                      k (s, mkEQ(sort, e1, e2))
                  else
                      let val _ =
                          if free a r then raise Option else ()
                      in
                          case attempt (a, subst s r) s of
                              NONE => k (s, mkEQ(sort, e1, e2))
                            | SOME s' => let (* val _ = checkOK s' *)
                                             val s' = applyToSelf s'
                                             val eq' = Constraint.subst s' (mkEQ(sort, e1, e2))
                                         in
                                             k (s', eq')
                                         end
                      end
              end
  and eliminate attempt a s W k = eliminate' attempt a s W k

  fun attempt (a, e) s =
              let val s' = (a, e) :: s
                  val _ = dprint (fn () => "attempt: replacing " ^ IV.toString a ^ " |-> " ^ Exp.toString e)
              in
                  SOME (map (fn (x, e) => (x, subst s' e)) s')
              end

  fun finishElim (s, W0') =
      (s, Constraint.subst s W0')

  fun xxElimExistential (S as STATE{exiSub= exiSub, ...}) (a, W0) fail succ =
      let val (s, W') = eliminate (attempt) a (EStoList exiSub) W0 finishElim 
(*          val _ = print ("\nforceElimExistential (" ^ IV.toString a ^ "): exiSub=  " ^ exiSubToString exiSub ^ "\n")
          val _ = print ("\nforceElimExistential (" ^ IV.toString a ^ ") obtained this constraint:\n\n" ^ Constraint.toString W' ^ "\n\n")*)
      in
          if Constraint.free a W' then
              fail (s, (a, W'))
          else
              succ (s, W')
      end

  fun forceElimExistential (S as STATE{exiSub= exiSub, ...}) (W as EXISTS(a, sort, W0)) =
      xxElimExistential
        S
        (a, W0)
        (fn (s, (a, W')) =>
         let val _ = print ("forceElimExistential left free existential "
                            ^ IndexSym.toString a
                            ^ ": will consider it universal during final validation\n")
         in
               (S, EXISTS(a, sort, W'))
         end)
        (fn (s, W') =>
         let val S = update_exiSub S (fn exiSub => valOf (ExiSub.merge exiSub (valOf (ExiSub.fromList s))))
         in
             (S, W')
         end)

  fun smearTuples W =
      case W of
          TRUE => W
        | AND(W1, W2) => AND(smearTuples W1, smearTuples W2)
        | OR(W1, W2) => OR(smearTuples W1, smearTuples W2)
        | IMPLIES(W1, W2) => IMPLIES(smearTuples W1, smearTuples W2)
        | ALL(b, sort, W0) => ALL(b, sort, smearTuples W0)
        | EXISTS(b, sort, W0) => EXISTS(b, sort, smearTuples W0)
        | PRED _ => W
        | EQ(Product sorts, Tuple e1, Tuple e2) => foldl mkAND TRUE (map mkEQ (MyList.zip3 (sorts, e1, e2)))
        | EQ(sort, e1, e2) => W

  fun isValid (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context}) =
      let val W = smearTuples W
          val W = dimlate [] W
          val W = debooleanate assn W
          val _ = dprint (fn () => "Solve.isValid(" ^ stateToString S ^ ")\n")

          fun cleanAssn W [] = W
            | cleanAssn W (Iprop P :: assn) = (cleanAssn (mkIMPLIES(P, W)) assn)
            | cleanAssn W ( _ :: assn) = cleanAssn W assn

          val W = cleanAssn W assn

          fun eliminateFreeExistentials [] s W =
              finishElim (s, W)
            | eliminateFreeExistentials (assn :: assns) s W =
                let in case assn of
                    Iexists(a, sort) =>
                        eliminate (attempt) a s W
                        (fn (s, W) => eliminateFreeExistentials assns s W)
                  | _ => eliminateFreeExistentials assns s W
                end

          val (s, W) = eliminateFreeExistentials assn [] W
                       (*XXX s *)
      in
          isValid' (updateConstraint S W)
      end

  and isValid' (S as STATE{assn= assn, exiSub= exiSub, context= context, constraint= W}) =
          let val _ = dprint (fn () => "Solve.isValid'(" ^ stateToString S ^ ")\n")
          in
              case W of
                  TRUE => true

                | AND(W1, W2) =>
                      isValid' (updateConstraint S W1) andalso isValid' (updateConstraint S W2)

                | OR(W1, W2) =>
                      let 
                          val _ = print "{{{{{{{{{\n"
                          val result = isValid' (updateConstraint S (IMPLIES(U.negate W1, W2)))
                          val _ =  print ("OR(" ^ Constraint.toString W1 ^ ", " ^ Constraint.toString W2 ^ ")   " ^
                                          Bool.toString result ^ "\n")
                          val _ = print "}}}}}}}}}\n"
                      in
                          result
                      end

                | ALL(a, sort, W0) =>
                      U.resultize context ((dprint (fn () => "UDS-2a: " ^ IndexSym.toString a); U.declare) (context, (a, sort)))
                        (fn _ => false)
                        (fn context => 
                         isValid' (frame (fn()=>"isValid':ALL") okSTATE{assn= Iall(a, sort) :: assn,
                                         exiSub= exiSub,
                                         context= context,
                                         constraint= W0}))

                | EXISTS(a, sort, W0) =>
                      U.resultize context ((dprint (fn () => "UDS-2e: " ^ IndexSym.toString a); U.declare) (context, (a, sort)))
                        (fn _ => false)
                        (fn context => 
                         isValid' (frame (fn()=>"isValid':EXISTS") okSTATE{assn= Iexists(a, sort) :: assn,
                                         exiSub= exiSub,
                                         context= context,
                                         constraint=
                                             let val (s, W) = eliminate (attempt) a [] W0 finishElim
                                             in
                                                 W  (* XXX s *)
                                             end}))

                | EQ(sort, e1, e2) => 
                      let val _ = dprint (fn () => "%%% exiSub = " ^ exiSubToString exiSub )
                          val _ = dprint (fn () => "%%% EQ " ^ Exp.toString e1 ^ "  =  " ^ Exp.toString e2)
                      in case Constraint.subst (EStoList exiSub) (mkEQ (sort, e1, e2)) of
                             TRUE => true
                           | EQ(sort, e1, e2) =>
                               U.isValidEq (fn W' =>
                                                 isValid' (STATE{assn= assn, exiSub= exiSub, context=context, constraint= W'}))
                                             (context, sort, (e1, e2))
                      end

                | PRED(p, e) =>
                      let val _ = dprint (fn () => "%%%% exiSub = " ^ exiSubToString exiSub )
                          val _ = dprint (fn () => "%%% PRED " ^ Exp.toString e)
                          val e = subst (EStoList exiSub) e
                      in
                          U.isValidPred (context, (p, e))
                      end

                | IMPLIES(W1, W2) =>
                      let
(*                                                (* !!!!!! *)  val exiSub = ExiSub.empty
XXXX                         val S = update_exiSub S (fn _ => exiSub)
*)
                          val result = 
                               case U.assert (context, W1, varMaker (assn, W)) of
                                  (U.Unsat, []) => true
                                | (U.Valid, djs) => (*DJS LOST*) isValid' (updateConstraint S W2)
                                | (U.Ok (context, eqs1), djs) => (*DJS LOST*)
                                                                 isValid' (frame (fn()=>"isValid':IMPLIES") okSTATE{assn= assn,
                                                                        exiSub= exiSub,
                                                                        context= context,
                                                                        constraint= W2})
                      in
                          result
                      end
          end


(* All combinations of djs1, djs2 *)
  fun compose djs1 [] = djs1
    | compose [] djs2 = djs2
    | compose djs1 djs2 =
        List.concat (map (fn dj1 => List.map (fn dj2 => mkAND(dj1, dj2)) djs2) djs1)

  fun takeAlong disjuncts1 (result, disjuncts2) =
      (result, compose disjuncts1 disjuncts2)

  fun poundExistentials S exis W =
      let in case exis of
          [] => (S, W)
        | exi::exis =>
              let in
                xxElimExistential S (exi, W)
                  (*fail: *) (fn (_, (_, W)) => (S, W))
                  (*succ: *) (fn (s, W) => (update_exiSub S (fn exiSub => valOf (ExiSub.merge exiSub (valOf (ExiSub.fromList s)))), W))
              end
      end

  datatype oilcan = ANTEC | IMPLIC of constraint | WHATEVER
  fun isOilcan W =
      let fun isAntec W =
          case W of
              PRED(p,Tuple[Literal(_,"111"),Literal(_,"222")]) => true
            | _ => false
      in
          case W of
              IMPLIES(W1,W2) => if isAntec W1 then IMPLIC W2 else WHATEVER
            | W => if isAntec W then ANTEC else WHATEVER
      end

(*
  fun rollback (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context}) =
      frame "rollback" okSTATE{assn= assn, constraint= W, exiSub= exiSub,
            context= U.rollback context}
*)

  fun finalCheck (S1 as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context, ...}) =
      let val _ = dprint (fn () => "Solve.finalCheck(" ^ stateToString S1 ^ ")\n")
(*          val eqs = U.getEqs context (varMaker (assn, W)) *)
          val suppl = (* supplement assn exiSub eqs *) []
(*          val S1 as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context} = S1 *)
(*          val _ = dprint (fn () => "Solve.finalCheck: S1 = " ^ stateToString S1 ) *)
(*          val S2 = frame (fn () => "finalCheck-S2") (okSTATE S1) *)
(*Constraint.subst suppl W*)
(*          val _ = dprint (fn () => "Solve.finalCheck: S2 = " ^ stateToString S2 ) *)
      in
          isValid S1
      end

  fun accumulate (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context},
                  Wnew) =
      let (* val _ = print ("Wnew " ^ Constraint.toString Wnew ^ "\n") *)
          val (Wnew, exiSub') = normalize assn exiSub Wnew
(*      val _ = print ("Wnew " ^ Constraint.toString Wnew ^ "\n")
      val _ = print (" exiSub' " ^ ExiSub.toString exiSub' ^ "\n") *)
          val exiSub = valOf (ExiSub.merge exiSub' exiSub)
          val S = update_exiSub S (fn _ => exiSub)

          fun sortVars vars =
              List.map (fn Iexists(a, _) => a) (List.filter (fn Iexists(a', _) => MyList.contains a' vars | _ => false) assn)

          val exis = collectExistentials S Wnew

          val exis = sortVars exis
(*          val _ = print ("@@ " ^ Int.toString (length exis) ^ "\n") *)
          val (S, Wnew') (*XXX (_, _)*) = poundExistentials S exis Wnew
(*          val _ = if Wnew = Wnew' then print ("===  " ^ Constraint.toString Wnew ^ "\n\n")
              else let in print ("NNN  " ^ Constraint.toString Wnew ^ "\n");
                  print ("YYY  " ^ Constraint.toString Wnew' ^ "\n\n")
                  end *)
(*          val Wnew = Wnew' *)
(*          val S = STATE{assn= assn, constraint= W, exiSub= exiSub, context= context} *)

(*          val Wnew = case isOilcan Wnew of
                    WHATEVER => Wnew
                  | ANTEC => (print ("accumulate oilcan: " ^ Constraint.toString Wnew ^ "\n");
                          Wnew)
                  | IMPLIC W2 => (print ("accumulate oilcan: LOSING oilcan!: " ^ Constraint.toString Wnew ^ "\n");
                          W2)
*)
      in
        case Wnew of
          TRUE => SOME (S, [])

        | AND(W1, W2) =>
              let in case accumulate (S, W1) of
                  NONE => NONE
                | SOME (S, djs1) =>
                      Option.map (takeAlong djs1) (accumulate (S, W2))
              end

        | IMPLIES(W1, W2) =>
              if (noExistentials S Wnew) andalso (!r_earlyValidation) then
                  let in case isValid (STATE{assn= assn, constraint= Wnew, exiSub= exiSub, context= context}) of
                      false => NONE
                    | true => SOME (S, [])   (*(STATE{assn= assn, constraint= mkAND(W, Wnew), exiSub= exiSub, context= context}) *)
                  end
              else
                  let in case assert false S W1 of
                      (Unsat, _) => SOME (S, [])  (* (FALSE => P)  ==  TRUE   for all P *)
                    | (Valid, djs) => (* The antecedent W1 amounted to TRUE, providing no new information,
                                         so just accumulate W2 *)
                          accumulate (S, W2)
                    | (Okay S1, djs) =>  SOME (frame (fn () => "accumulate:IMPLIES "
                                                             ^ stateToString S ^ "  +++1  " ^ Constraint.toString Wnew)
                                                     okSTATE{assn= assn, constraint= mkAND(W, mkIMPLIES(W1, W2)), exiSub= exiSub, context= context},
                                       [])
                  end

        | ALL(aa, sort, W0) =>
              let val a = IndexSym.new aa
                  val W0 = Constraint.subst [(aa, Uvar a)] W0
                  val aa = ()
                  val assn' = (Iall (a, sort)) :: assn
                  val S' = frame (fn () => "accumulate:ALL")
                                 okSTATE{assn= assn',
                                         constraint= W,
                                         exiSub= exiSub,
                                         context=
                                             (case ( (* print ("UDS-3: " ^ IndexSym.toString a ^ "\n"); *)
                                                    U.declare) (context, (a, sort))
                                               of
                                                  U.Valid => context
                                                | U.Ok(context, _) => context)   (* joshua 2011-01-24 *)
                                        }
              in
                  accumulate (S', W0)
              end

        | EXISTS(aa, sort, W0) =>
              let val assn' = (Iexists (aa, sort)) :: assn
                  val S' = frame (fn () => "accumulate:EXISTS") okSTATE{assn= assn', constraint= W, exiSub= exiSub, context= context}
              in
                  accumulate (S', W0)
              end

        | OR _ => 
              let in
                 print ("accumulate OR\n");
                 if (noExistentials S Wnew) andalso (!r_earlyValidation) then
                     let in case isValid (STATE{assn= assn, constraint= Wnew, exiSub= exiSub, context= context}) of
                         false => NONE
                       | true => SOME (S, [])   (*(STATE{assn= assn, constraint= mkAND(W, Wnew), exiSub= exiSub, context= context}) *)
                     end
                 else
                     let in case assert true S Wnew of
                         (Unsat, _) => NONE
                       | (Valid, djs) => SOME (S, djs)
                       | (Okay S', djs) => SOME (S', djs)
                     end
              end

        | _ => 
              if (noExistentials S Wnew) andalso (!r_earlyValidation) then
                  let in case isValid (STATE{assn= assn, constraint= Wnew, exiSub= exiSub, context= context}) of
                      false => NONE
                    | true => SOME (S, [])   (*(STATE{assn= assn, constraint= mkAND(W, Wnew), exiSub= exiSub, context= context}) *)
                  end
              else
                  let in case assert true S Wnew of
                      (Unsat, _) => NONE
                    | (Valid, djs) => SOME (S, djs)
                    | (Okay S', djs) => SOME (S', djs)
                  end
      end
  
  fun push (state as STATE{context, ...}) =
      let val (context, point) = U.push context
      in
          (update_context state (fn _ => context),
           point)
      end

  fun popto (state, point) =
      update_context state (fn context => U.popto (context, point))

  fun solve S =
      let in
          finalCheck S
      end

  fun ejectConstraint (S as STATE{assn= assn, constraint= W, exiSub= exiSub, context= context}) =
      (frame (fn () => "ejectConstraint")
         okSTATE{assn= assn, constraint= TRUE, exiSub= exiSub, context= context},
       W)

  fun unejectConstraint (S as STATE{assn= assn, constraint= W', exiSub= exiSub, context= context}, W) =
      frame (fn () => "ejectConstraint")
        okSTATE{assn= assn, constraint= mkAND(W, W'), exiSub= exiSub, context= context}

  fun gather W =
      case W of
          TRUE => []
        | AND(W1, W2) =>  gather W1 @ gather W2
        | ALL(a, sort, W0) => (IndexSym.toString a ^ " : " ^ "INTEGER" ^ ";") :: gather W0
        | EXISTS(a, sort, W0) => (IndexSym.toString a ^ " : " ^ "INTEGER" ^ ";") :: gather W0
        | IMPLIES(W1, W2) => gather W1 @ gather W2
        | EQ(_, e1, e2) => []
        | OR _ => raise Match
        | PRED _ => raise Match


  fun constraintfree x W =
      case W of
          TRUE => false
        | AND(W1, W2) => constraintfree x W1 orelse constraintfree x W2
        | OR(W1, W2) => constraintfree x W1 orelse constraintfree x W2
        | PRED (_, e) => free x e
        | ALL(a, sort, W0) => constraintfree x W0
        | EXISTS(a, sort, W0) => constraintfree x W0
        | IMPLIES(W1, W2) => constraintfree x W1 orelse constraintfree x W2
        | EQ(_, e1, e2) => free x e1 orelse free x e2

  fun simplify W =
      case W of
          TRUE => TRUE
        | PRED xx => PRED xx
        | AND(W1, W2) =>
              mkAND (simplify W1, simplify W2)
        | OR(W1, W2) =>
              mkOR (simplify W1, simplify W2)
        | ALL(a, sort, W0) => let in case simplify W0 of
              TRUE => TRUE
            | W0S => if constraintfree a W0S then ALL(a, sort, W0S) else W0S
                              end
        | EXISTS(a, sort, W0) => let in case simplify W0 of
              TRUE => TRUE
            | W0S => if constraintfree a W0S then EXISTS(a, sort, W0S) else W0S
                              end
        | IMPLIES(W1, W2) => let in
              case (simplify W1, simplify W2) of
                  (W1S, TRUE) => TRUE
                | (W1S, W2S) => mkIMPLIES(W1S, W2S)
                             end
        | EQ(sort, e1, e2) => if e1 = e2 then TRUE else mkEQ(sort, e1, e2)


  fun gather_context W =
      case W of
          TRUE => []
        | AND(W1, W2) =>  gather_context W1 @ gather_context W2
        | PRED(_, e1) => [] (* XXX *)
        | OR(W1, W2) =>  gather_context W1 @ gather_context W2
        | ALL(a, sort, W0) => ("sig " ^ IndexSym.toString a ^ " : " ^ "int" ^ ".") :: gather_context W0
        | EXISTS(a, sort, W0) => ("sig " ^ IndexSym.toString a ^ " : " ^ "int" ^ ".") :: gather_context W0
        | IMPLIES(W1, W2) => gather_context W1 @ gather_context W2
        | EQ(_, e1, e2) => []

  fun context_solve W = raise Option

  fun getConstraint (STATE{constraint, ...}) = constraint

  fun save (S as STATE{context, ...}) =
      let val (context', restorer) = U.save context
      in
          (update_context S (fn _ => context'),
           fn (S as STATE{context, ...}) => update_context S (fn _ => restorer context))
      end

  fun reset () =
      U.reset()
  
end (* functor SolveFn *)



(* It is recommended that you not abbreviate Solve. *)

structure Solve :> SOLVE = struct

  type point = int

(*  structure SIcs = SolveFn(structure U = Ics) *)
  structure SIcs = SolveFn (structure U = CvclPiped)  (* XXX: temporary (?) measure to expedite removal of Ics code  *)
  structure SYices = SolveFn (structure U = CvclPiped)  (* XXX: temporary (?) measure to expedite removal of Yices code  *)
  structure SCvcl = SolveFn (structure U = CvclPiped)  (* XXX: temporary (?) measure to expedite mothballing of Cvcl code  *)

  structure SCvclPiped = SolveFn (structure U = CvclPiped)
  structure SCvc4Piped = SolveFn (structure U = Cvc4Piped)
  
  val r_earlyValidation = ref true
  
  datatype which = Ics | Yices | Cvcl | CvclPiped | Cvc4Piped
(*  val switch = ref Cvcl (* Yices *)
*)
  val switch = ref Cvc4Piped (* Yices *)
  
  fun whichToString which = case which of
    Ics => "Ics"
  | Yices => "Yices"
  | Cvcl => "Cvcl"
  | CvclPiped => "CvclPiped"
  | Cvc4Piped => "Cvc4Piped"
  
  datatype state =
      IcsS of SIcs.state
    | YicesS of SYices.state
    | CvclS of SCvcl.state
    | CvclPipedS of SCvclPiped.state
    | Cvc4PipedS of SCvc4Piped.state
  
  type disjuncts = Indexing.constraint list
  
  exception SolverStartupFailed
  exception SolverFailure
  
  fun reset ()= 
      let in
          SIcs.reset();
          SYices.reset();
          SCvcl.reset();
          SCvclPiped.reset();
          SCvc4Piped.reset()
      end
  
  fun setConstraintSolver which =
     (switch := which;
      print ("Constraint solver set to " ^ whichToString which ^ "\n");
      reset ())

  fun cs which =
      setConstraintSolver (
      case (String.sub (which, 0)) handle _ => #"\n" of
          #"i" => Ics
        | #"y" => Yices
        | #"c" => Cvc4Piped
        | #"3" => Cvcl
        | #"p" => CvclPiped
        | _ => (print "\nValid arguments to Solve.cs are:\n  i* => Ics, y* => Yices, c* => Cvc4Piped (CVC4), p* => CvclPiped (CVC3), 3* => Cvcl (CVC3, direct)\n"; raise Match))

  fun which () = whichToString(!switch)
  
  fun empty () = case !switch of
      Ics => IcsS (SIcs.empty())
    | Yices => YicesS (SYices.empty())
    | Cvcl => CvclS (SCvcl.empty())
    | CvclPiped => CvclPipedS (SCvclPiped.empty())
    | Cvc4Piped => Cvc4PipedS (SCvc4Piped.empty())
  
  fun apply state fIcs fYices fCvcl fCvclPiped fCvc4Piped x =
      case (state, !switch) of
          (IcsS state, Ics) => IcsS (fIcs (state, x))
        | (YicesS state, Yices) => YicesS (fYices (state, x))
        | (CvclS state, Cvcl) => CvclS (fCvcl (state, x))
        | (CvclPipedS state, CvclPiped) => CvclPipedS (fCvclPiped (state, x))
        | (Cvc4PipedS state, Cvc4Piped) => Cvc4PipedS (fCvc4Piped (state, x))

  fun applyc state fIcs fYices fCvcl fCvclPiped fCvc4Piped x =
      case (state, !switch) of
          (IcsS state, Ics) => IcsS (fIcs state x)
        | (YicesS state, Yices) => YicesS (fYices state x)
        | (CvclS state, Cvcl) => CvclS (fCvcl state x)
        | (CvclPipedS state, CvclPiped) => CvclPipedS (fCvclPiped state x)
        | (Cvc4PipedS state, Cvc4Piped) => Cvc4PipedS (fCvc4Piped state x)

  fun applycOpt state fIcs fYices fCvcl fCvclPiped fCvc4Piped x =
      case (state, !switch) of
          (IcsS state, Ics) => Option.map IcsS (fIcs state x)
        | (YicesS state, Yices) => Option.map YicesS (fYices state x)
        | (CvclS state, Cvcl) => Option.map CvclS (fCvcl state x)
        | (CvclPipedS state, CvclPiped) => Option.map CvclPipedS (fCvclPiped state x)
        | (Cvc4PipedS state, Cvc4Piped) => Option.map Cvc4PipedS (fCvc4Piped state x)

  fun applyOpt state fIcs fYices fCvcl fCvclPiped fCvc4Piped x =
      case (state, !switch) of
          (IcsS state, Ics) => Option.map IcsS (fIcs (state, x))
        | (YicesS state, Yices) => Option.map YicesS (fYices (state, x))
        | (CvclS state, Cvcl) => Option.map CvclS (fCvcl (state, x))
        | (CvclPipedS state, CvclPiped) => Option.map CvclPipedS (fCvclPiped (state, x))
        | (Cvc4PipedS state, Cvc4Piped) => Option.map Cvc4PipedS (fCvc4Piped (state, x))

  fun applyList state fIcs fYices fCvcl fCvclPiped fCvc4Piped x =
      case (state, !switch) of
          (IcsS state, Ics) => List.map IcsS (fIcs (state, x))
        | (YicesS state, Yices) => List.map YicesS (fYices (state, x))
        | (CvclS state, Cvcl) => List.map CvclS (fCvcl (state, x))
        | (CvclPipedS state, CvclPiped) => List.map CvclPipedS (fCvclPiped (state, x))
        | (Cvc4PipedS state, Cvc4Piped) => List.map Cvc4PipedS (fCvc4Piped (state, x))

  fun apply1 state fIcs fYices fCvcl fCvclPiped fCvc4Piped =
      case (state, !switch) of
          (IcsS state, Ics) => IcsS (fIcs (state))
        | (YicesS state, Yices) => YicesS (fYices (state))
        | (CvclS state, Cvcl) => CvclS (fCvcl (state))
        | (CvclPipedS state, CvclPiped) => CvclPipedS (fCvclPiped (state))
        | (Cvc4PipedS state, Cvc4Piped) => Cvc4PipedS (fCvc4Piped (state))

  fun apply10 state fIcs fYices fCvcl fCvclPiped fCvc4Piped  =
      case (state, !switch) of
          (IcsS state, Ics) => fIcs (state)
        | (YicesS state, Yices) => fYices (state)
        | (CvclS state, Cvcl) => fCvcl (state)
        | (CvclPipedS state, CvclPiped) => fCvclPiped (state)
        | (Cvc4PipedS state, Cvc4Piped) => fCvc4Piped (state)

  fun applyc0 state fIcs fYices fCvcl fCvclPiped  fCvc4Piped x =
      case (state, !switch) of
          (IcsS state, Ics) => fIcs (state) x
        | (YicesS state, Yices) => fYices (state) x
        | (CvclS state, Cvcl) => fCvcl (state) x
        | (CvclPipedS state, CvclPiped) => fCvclPiped (state) x
        | (Cvc4PipedS state, Cvc4Piped) => fCvc4Piped (state) x

  fun apply1P state fIcs fYices fCvcl fCvclPiped fCvc4Piped  =
      case (state, !switch) of
          (IcsS state, Ics) => let val (state', rest) = fIcs state in (IcsS state', rest) end
        | (YicesS state, Yices) => let val (state', rest) = fYices state in (YicesS state', rest) end
        | (CvclS state, Cvcl) => let val (state', rest) = fCvcl state in (CvclS state', rest) end
        | (CvclPipedS state, CvclPiped) => let val (state', rest) = fCvclPiped state in (CvclPipedS state', rest) end
        | (Cvc4PipedS state, Cvc4Piped) => let val (state', rest) = fCvc4Piped state in (Cvc4PipedS state', rest) end

  fun apply1PA state fIcs fYices fCvcl fCvclPiped  fCvc4Piped arg =
      case (state, !switch) of
          (IcsS state, Ics) => let val (state', rest) = fIcs state arg in (IcsS state', rest) end
        | (YicesS state, Yices) => let val (state', rest) = fYices state arg in (YicesS state', rest) end
        | (CvclS state, Cvcl) => let val (state', rest) = fCvcl state arg in (CvclS state', rest) end
        | (CvclPipedS state, CvclPiped) => let val (state', rest) = fCvclPiped state arg in (CvclPipedS state', rest) end
        | (Cvc4PipedS state, Cvc4Piped) => let val (state', rest) = fCvc4Piped state arg in (Cvc4PipedS state', rest) end
      
  fun accumulate (state, constraint) =
      case (state, !switch) of
          (IcsS state, Ics) => Option.map (fn (state', rest) => (IcsS state', rest)) (SIcs.accumulate (state, constraint))
        | (YicesS state, Yices) => Option.map (fn (state', rest) => (YicesS state', rest)) (SYices.accumulate (state, constraint))
        | (CvclS state, Cvcl) => Option.map (fn (state', rest) => (CvclS state', rest)) (SCvcl.accumulate (state, constraint))
        | (CvclPipedS state, CvclPiped) => Option.map (fn (state', rest) => (CvclPipedS state', rest)) (SCvclPiped.accumulate (state, constraint))
        | (Cvc4PipedS state, Cvc4Piped) => Option.map (fn (state', rest) => (Cvc4PipedS state', rest)) (SCvc4Piped.accumulate (state, constraint))

  fun assume (state, constraint) =
      case (state, !switch) of
          (IcsS state, Ics) => Option.map (fn (state', rest) => (IcsS state', rest)) (SIcs.assume (state, constraint))
        | (YicesS state, Yices) => Option.map (fn (state', rest) => (YicesS state', rest)) (SYices.assume (state, constraint))
        | (CvclS state, Cvcl) => Option.map (fn (state', rest) => (CvclS state', rest)) (SCvcl.assume (state, constraint))
        | (CvclPipedS state, CvclPiped) => Option.map (fn (state', rest) => (CvclPipedS state', rest)) (SCvclPiped.assume (state, constraint))
        | (Cvc4PipedS state, Cvc4Piped) => Option.map (fn (state', rest) => (Cvc4PipedS state', rest)) (SCvc4Piped.assume (state, constraint))

  fun save state =
      case (state, !switch) of
          (IcsS state, Ics) => let val (state', rest) = SIcs.save state in (IcsS state', fn IcsS state => IcsS (rest state)) end
        | (YicesS state, Yices) => let val (state', rest) = SYices.save state in (YicesS state', fn YicesS state => YicesS (rest state)) end
        | (CvclS state, Cvcl) => let val (state', rest) = SCvcl.save state in (CvclS state', fn CvclS state => CvclS (rest state)) end
        | (CvclPipedS state, Cvcl) => let val (state', rest) = SCvclPiped.save state in (CvclPipedS state', fn CvclPipedS state => CvclPipedS (rest state)) end
        | (Cvc4PipedS state, Cvcl) => let val (state', rest) = SCvc4Piped.save state in (Cvc4PipedS state', fn Cvc4PipedS state => Cvc4PipedS (rest state)) end

  fun ejectConstraint state =
      apply1P state
              SIcs.ejectConstraint SYices.ejectConstraint SCvcl.ejectConstraint SCvclPiped.ejectConstraint SCvc4Piped.ejectConstraint
  
  fun unejectConstraint (state, constraint) =
      apply state
            SIcs.unejectConstraint
            SYices.unejectConstraint
            SCvcl.unejectConstraint
            SCvclPiped.unejectConstraint
            SCvc4Piped.unejectConstraint
            constraint

  fun forceElimExistential state arg =
      apply1PA state
               SIcs.forceElimExistential SYices.forceElimExistential SCvcl.forceElimExistential SCvclPiped.forceElimExistential SCvc4Piped.forceElimExistential
               arg

  fun solve state =
      apply10 state
              SIcs.solve SYices.solve SCvcl.solve SCvclPiped.solve SCvc4Piped.solve

  val compose = SIcs.compose
  fun takeAlong arg state = SIcs.takeAlong arg state
  
  fun getConstraint state = 
      apply10 state
              SIcs.getConstraint SYices.getConstraint SCvcl.getConstraint SCvclPiped.getConstraint  SCvc4Piped.getConstraint

  fun addUniversalAssn state arg =
      applycOpt state
             SIcs.addUniversalAssn SYices.addUniversalAssn SCvcl.addUniversalAssn
             SCvclPiped.addUniversalAssn
             SCvc4Piped.addUniversalAssn
             arg
  fun addExistentialAssn state arg =
      applycOpt state
             SIcs.addExistentialAssn SYices.addExistentialAssn SCvcl.addExistentialAssn SCvclPiped.addExistentialAssn SCvc4Piped.addExistentialAssn
             arg
  fun stateToString state =
      apply10 state SIcs.stateToString SYices.stateToString SCvcl.stateToString SCvclPiped.stateToString SCvc4Piped.stateToString
  fun ok_state state =
      apply1 state SIcs.ok_state SYices.ok_state SCvcl.ok_state SCvclPiped.ok_state  SCvc4Piped.ok_state 

  fun knowsSym state a =
      applyc0 state
              SIcs.knowsSym SYices.knowsSym SCvcl.knowsSym
              SCvclPiped.knowsSym
              SCvc4Piped.knowsSym
              a

  fun push state =
      case (state, !switch) of
          (Cvc4PipedS state, Cvc4Piped) =>
              let val (context, result) = SCvc4Piped.push state
              in
                  (Cvc4PipedS context, result)
              end

  fun popto (state, arg) = 
      case (state, !switch) of
          (Cvc4PipedS state, Cvc4Piped) =>
              Cvc4PipedS (SCvc4Piped.popto (state, arg))

end (* structure Solve *)
