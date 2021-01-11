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
(* File: Sortcheck.sml
   Author: Joshua Dunfield
   Contents: Sort checking:
 
      - In each occurrence of tau(i), check that tau is index-refined (by some sort) and that   i : sort

   History:
      2004-08-08 [jcd] -- Created.
      2004-09-13 [jcd] -- Added support for INil.
*)

signature SORTCHECK = sig
 
  val check : Sdml.program -> (bool * Sdml.program)

end

structure Sortcheck :> SORTCHECK = struct

(************************
  fun check (Program(libinfo as Libinfo{primtcs= primtcs, primops= primops}, typedecs, locexp)) = 
          fun transform_texp texp =
              case texp of
                  Tycon(tc, NONE, polytexps) =>
                      let in case get_sort_opt tc of
                          NONE => texp   (* Type `tc' is not refined:  Leave as is *)
                        | SOME sort => (* Type `tc' is refined:  Add existential quantifier *)
                              let val ex = IndexSym.fresh "ex"
                              in
                                  Exis(ex, sort, Tycon(tc, SOME (X.Evar ex), polytexps))
                              end
                      end
                | texp => texp
                      
************************)

    open Sdml
    structure CC = Sdml.ConcreteContext
    structure X = Indexing
    structure DS = Datasorts
    type constraint = X.constraint

    
    structure IAE = IntStatistEnv
    structure PVAE = PVStatistEnv
    structure TCAE = TCStatistEnv
    structure PP = PrettyPrint

    val bogus_loc = Location.fromPositions (1, 1, 1, 1)

    val {dprint, dprnt} =
        Debug.register {full_name= "Sortcheck",
                        short_name= "Sortcheck"}
    
    local
        val index = Option.valOf (Debug.from "Sortcheck")
    in
        fun fail s =
            Debug.makeFail index s
    end

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
      | Tuple   _ => "Tuple"
      | Merge   _ => "Merge"
      | Proj(fld,_) => "Proj(" ^fld ^ ", _)"
      | Let    _ => "Let"
      | Lethint   _ => "Lethint"
      | Anno   _ => "Anno"
      | LET(pv,_,_) => "LET("^PV.toString pv ^",...)"
(*      | LETDN(pv,_,_) => "LETDN("^PV.toString pv ^",...)" *)
      | LETSLACK(pv,_,_) => "LETSLACK("^PV.toString pv ^",...)"
      | Raise _ => "Raise"
      | Handle _ => "Handle"
      | Spy _ => "Spy"
      | Leftanno _ => "Leftanno"
        end

  datatype indexassumption =
      Iall of IndexSym.sym * X.sort
    | Iexists of IndexSym.sym * X.sort

  fun lookupIndex sym [] = fail ("lookupIndex: " ^ IndexSym.toString sym ^ " not found")
    | lookupIndex sym ((assn as Iall(sym', sort)) :: rest) = if sym=sym' then assn else lookupIndex sym rest
    | lookupIndex sym ((assn as Iexists(sym', sort)) :: rest) = if sym=sym' then assn else lookupIndex sym rest

  fun indexassumptionToString assn =
      case assn of
          Iall(sym, sort) => IndexSym.toShortString sym ^ " :A: " ^ X.Sort.toString sort
        | Iexists(sym, sort) => IndexSym.toShortString sym ^ " :E: " ^ X.Sort.toString sort

  fun indexToString l = Separate.list ",  " (map indexassumptionToString l)

  type ctx = indexassumption list

  fun ctxToString ctx = indexToString ctx
  
  fun %% (ctx, indexassn) = indexassn :: ctx
  infix 5 %%

  val empty_ctx = []

  fun check_program (Program (libinfo as Libinfo{primtcs, primops, distinguished}, lib_decs, body)) =
    let
(*       val _ = print ("Sortcheck: " ^ Int.toString (List.length lib_decs) ^ "\n") *)
(*    fun get_cons_alg (Datatype (_, _, _, cons)) = map (fn Constructor{c= c, ...} => (c, ())) cons
    fun get_cons_algs typedecs = List.concat (map get_cons_alg typedecs)
    fun get_cons_algsl typedecsl = List.concat (map get_cons_algs typedecsl)
*)
    
    fun failloc loc why = fail (why ^ " @ " ^ Location.toString loc)

    val tcAssocFromLibinfo = primtcs
(*    val tcAssoc : (tc * Indexing.Sorting.t) list = tcAssocFromLibinfo *)

    val context = tcAssocFromLibinfo

    fun get_sort_opt context tc =
        let val base_tc = case Datasorts.refines tc of SOME tc' => tc' | NONE => tc
        in
            case Assoc.getOpt context base_tc of
                SOME stuff => stuff
              | NONE => (print ("get_sort_opt: " ^ TC.toString tc ^ " not found\n"); raise Option)
        end
    val get_sort_opt = (get_sort_opt : (Sdml.tc * Indexing.Sorting.t) list -> Sdml.tc -> Indexing.Sorting.t)

    fun amend1 s1 s2 = case (s1, s2) of
       (X.Sorting.None, s2) => s2
     | (s1, X.Sorting.None) => s1
     | (X.Sorting.Nameless _, _) => fail ("amend1 trying to amend nameless")
     | (_, X.Sorting.Nameless _) => fail ("amend1 trying to amend with nameless")
     | (X.Sorting.Fields origFields, X.Sorting.Fields moreFields) =>
         let val result =
           X.Sorting.Fields (origFields @ moreFields)   (* XXX: check for clashes *)
         in
         ( print ("amending: new sorting: " ^ X.Sorting.toString result ^ "\n")
           ; result)
         end

    fun amendSorting context tc sorting = case context of
       [] => []
     | (tc1, sorting1) :: rest =>
          if tc=tc1 then (tc1, amend1 sorting1 sorting) :: rest
          else (tc1, sorting1) :: (amendSorting rest tc sorting)
    
    fun check context loc ctx i sort =
       let val sort' = infer context loc ctx i
       in
           if X.subsort (sort', sort) then
               sort
           else
               failloc loc ("expected sort " ^ X.Sort.toString sort ^ ", got sort " ^ X.Sort.toString sort')
       end

   and infer context loc ctx i =
       let val infer = infer context loc
           val fail = failloc loc
       in
         case i of
             X.Uvar a =>
                 let in case lookupIndex a ctx of
                     Iall(_, sort) => sort
                   | Iexists(_, sort) => (print ("Warning (Sortcheck): Iexists/Iall variable error\n"); sort)
                 end
           | X.Nil a =>
                 let in case X.getSyminfo a of
                     SOME (X.INil sort) => sort
                   | _ => fail ("unknown Nil-symbol ``" ^ IndexSym.toString a ^ "''")
                 end

           | X.NODIM => X.Base (X.getDimSort() )
           | X.BaseDim _ => X.Base (X.getDimSort() )

           | X.True => X.Base (X.getBoolSort() )
           | X.False => X.Base (X.getBoolSort() )

           | X.Evar a => let in case lookupIndex a ctx of
                 Iall(_, sort) => (print ("Warning (Sortcheck.sml): all/exists variable error\n"); sort)
               | Iexists(_, sort) => sort
                         end
           | X.Literal(basesortname, _) => X.Base basesortname
           | X.App(fsym, exp) => 
                 let in case X.getSyminfo fsym of
                     SOME (X.IFun components) =>
                     (* Index functions have a very poor excuse for intersection sorts:
                      I don't expect this to work properly unless the components of the
                      pseudo-intersection have disjoint domains, because there is no backtracking.
                      *)
                     let fun tryAll failure f [] = failure()
                             | tryAll failure f (x::xs) = (f x) handle _ => tryAll failure f xs
                         fun try {domain, range, complement} =
                             let val _ = check context loc ctx exp domain
                             in
                                 range
                             end
                     in
                         tryAll (fn _ => fail ("sort mismatch in index expression containing function symbol ``" ^ IndexSym.toShortString fsym ^ "''"))
                           try components
                     end
                   | NONE => fail ("unknown symbol ``" ^ IndexSym.toShortString fsym ^ "''")
                   | sort => fail ("``" ^ IndexSym.toShortString fsym ^ "'' is not an index function")
                 end
           | X.Tuple exps => X.Product (map (infer ctx) exps)
           | X.Proj(n, exp) =>
                 let in case infer ctx exp of
                     sort as X.Product sorts =>
                         let in 
                             (List.nth (sorts, n - 1))
                             handle Subscript =>
                                 fail ("projection #" ^ Int.toString n ^" applied to object of sort " ^ X.Sort.toString sort)
                         end
                   | sort => fail ("projection applied to object of sort " ^ X.Sort.toString sort)
                 end
       end

    fun prop_ok P =
        ()   (* XXX *)
    
    fun t_ok context loc ctx texp =
        let val t_ok = t_ok context loc
            val fail = failloc loc

            fun checkIndexAgainstSpec i (sort, default) =
              let val _ = check context loc ctx i sort in
                ()
              end

            fun checkRecordAgainstSorting record sorting = case record of 
              X.I fields => List.app (fn (fieldname, i) =>
                                                 let in case sorting of X.Sorting.Fields list =>
                                                   let in case Assoc.getOpt list fieldname of
                                                       NONE => fail ("Given field \"" ^ IndexFieldName.toShortString fieldname
                                                          ^ "\" not present in " ^ X.Sorting.toString sorting)

                                                     | SOME spec => checkIndexAgainstSpec i spec
                                                    end
                                                | _ => fail ("Field " ^ IndexFieldName.toShortString fieldname
                                                   ^ " given, but sorting is " ^ X.Sorting.toString sorting)
                                                 end)
                                     fields
           | X.N => ()
           | X.O i => let in case sorting of
                               X.Sorting.Nameless spec => checkIndexAgainstSpec i spec
                            | _ => fail ("Nameless index " ^ X.Exp.toString i
                                           ^ " given, but sorting is " ^ X.Sorting.toString sorting)
                             end
        in
          case texp of
              Typevar _ => ()
            | All(tv, uu, texp) => t_ok ctx texp
            | Extypevar _ => () (* XXX---"must" be a use of a type synonym *)
            | Arrow(dom, range) => (t_ok ctx dom; t_ok ctx range)
            | Product texps => List.app (t_ok ctx) texps
            | Tycon(tc, record, texps) =>
                 (checkRecordAgainstSorting record (get_sort_opt context tc);
                  List.app (t_ok ctx) texps)
            | Sect(A1, A2) => (t_ok ctx A1; t_ok ctx A2)
            | Union(A1, A2) => (t_ok ctx A1; t_ok ctx A2)
            | Univ(sym, sort, A) => t_ok (Iall(sym, sort) :: ctx) A
            | Exis(sym, sort, A) => t_ok (Iexists(sym, sort) :: ctx) A
            | Top => ()
            | Bot => ()
            | Implies(P, A) => (prop_ok P; t_ok ctx A)
            | Record(fld, A) => (t_ok ctx A)
            | Conj(P, A) => (prop_ok P; t_ok ctx A)
        end

    fun texp_ok context loc texp =
        t_ok context loc empty_ctx texp

    fun exp_ok context (loc, exp) =
      let val ok = exp_ok context
      in
        case exp of
            Const(texp, _) => ()
          | Var pv => ()
          | Con c => ()
          | Case(e1, arms) => (ok e1; List.app (arm_ok context) arms)
          | Fn(pv, e1) => ok e1
          | App(e1, e2) => (ok e1; ok e2)
          | RecordExp(fld, e1) => ok e1
          | Conapp(c, e1) => ok e1
          | Tuple es => List.app ok es
          | Merge es => List.app ok es
          | Proj(fld, e0) => ok e0
          | Let(decs, e0) => let val context = decs_ok context decs in exp_ok context e0 end
          | Lethint(anno, e1) => (annolist_ok context loc anno; ok e1)
          | Anno(e1 as (loc1,_), anno) => (ok e1; annolist_ok context loc1 anno)
          | LET(pv, e1, exp2) => (ok e1; ok (loc, exp2))
          | LETSLACK(pv, e1, exp2) => (ok e1; ok (loc, exp2))
          | Lvar X => ()
          | Raise e0 => ok e0
          | Handle (e1, pv, e2) => (ok e1; ok e2)
          | Spy (_, e0) => ok e0
          | Leftanno (_, e0) => ok e0 (* XXX *)
      end

    and arm_ok context (Arm(pattern, locexp as (loc,_))) =
        exp_ok context locexp

(*
    and ctxanno_ok context loc typings =
        let fun typing_ok (concrete_ctxt, texp) =
            let fun process_cc ctx [] = ctx
                  | process_cc ctx (CC.IndexVar(sym, sort) :: cc) = process_cc (Iall(sym, sort) :: ctx) cc
                  | process_cc ctx (CC.ProgramVar(pv, texp) :: cc) = (t_ok context loc ctx texp; process_cc ctx cc)
                  | process_cc ctx (CC.TypeVar(tv) :: cc) = (process_cc ctx cc)

                val ctx = process_cc empty_ctx concrete_ctxt
            in
                t_ok context loc ctx texp
            end
        in
            List.app typing_ok typings 
        end
*)
    and annolist_ok context loc annolist =
          let fun process_anno ctx anno = case anno of
                  AnnotationType.Type texp =>
                     t_ok context loc ctx texp

                | AnnotationType.Some (sym, sort, anno) =>
                       process_anno (Iall(sym, sort) :: ctx) anno
                | AnnotationType.LeftProgramVar (pv, texp, anno) =>
                      (t_ok context loc ctx texp;
                       process_anno ctx anno)
(*                  | (ANNO.TypeVar tv) :: anno =>
                      (process_anno ctx anno) *)

          in
              List.app (process_anno empty_ctx) annolist
          end

    and decs_ok context decs =
        let fun dec_ok context (loc, dec) = case dec of 
          ValType (pv, dectype) =>
             let in case dectype of
                  Dectype.AGAINST anno =>
                     (annolist_ok context loc anno;
                      context)
                | Dectype.TOPLEVEL_AGAINST texp =>
                     (texp_ok context loc texp;
                      context)
                | Dectype.TOPLEVEL_NOT texp =>
                     (texp_ok context loc texp;
                      context)
             end

       | Dec(pv, _, locexp) =>
             (exp_ok context locexp;
              context)

       | Typedec typedecs =>
             let fun extract (Datatype {tc, sorting, ...}) = (tc, sorting)
                   | extract (Synonym{tc, tv, params, definition}) = (tc, X.Sorting.None)  (* XXX *)
                 val context = context @ List.map extract typedecs
             in
               (typeinfer_algs context typedecs;
                context)
             end

       | DatatypeWith (tc, sorting) =>
            let val context = amendSorting context tc sorting
            in
               context
            end
       
       | _ => context
     in
         case decs of
            [] => context
          | d::ds => decs_ok (dec_ok context d) ds
     end

    and typeinfer_con context (Constructor {c, nullary, basetype, contype, ...(*XXX*) }) =
            (texp_ok context bogus_loc basetype;
             texp_ok context bogus_loc contype)

    and typeinfer_cons context sort cons = List.app (typeinfer_con context) cons

    and typeinfer_alg context (Datatype {tc, sorting, constructors, ...}) = typeinfer_cons context sorting constructors
      | typeinfer_alg context (Synonym {tc, tv, params, definition}) =
                texp_ok context bogus_loc definition   (* XXX *)

    and typeinfer_algs context typedecs = List.app (typeinfer_alg context) typedecs
    
(*
    fun typeinfer_algsl context typedecsl = List.app (typeinfer_algs context) typedecsl

    val context = context @ (map (fn Datatype(tc, _, sorting, cons) => (tc, sorting)) (List.concat typedecsl))

    val _ = typeinfer_algsl context typedecsl
    val _ = exp_ok context body
*)
    val result = Program (libinfo, lib_decs, body)
    in
        result
    end

    fun check program =
        let in
            (true, check_program program)
            before
            print "Sortchecking succeeded.\n"
        end
        handle Debug.StdExcept(s1, s2) => (print ("\n" ^ s1 ^ " " ^ s2 ^ "\n");
                                           (false, program))

end
