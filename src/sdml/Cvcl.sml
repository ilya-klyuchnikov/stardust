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
structure Cvcl :> SOLVER_INTERFACE_CVCL = struct

      val canHandleBooleans = true
      fun negate x = raise Option

      val {dprint, ... (*dprnt  Thou shalt not use dprnt*)} =
          Debug.register {full_name= "Cvcl",
                          short_name= "Cvcl"}

      fun getLocation () = NONE (* (Stardustrc.get (fn Stardustrc.Cvcl loc => loc)) *)

      val transactionCount = ref 0
      val rollbackCount = ref 0
      val rollbackWeight = ref 0 
      fun printResetCounts () =
          (print ("transactionCount  = " ^ Int.toString (!transactionCount) ^ "\n");
           print ("rollbackCount     = " ^ Int.toString (!rollbackCount) ^ "\n");
           print ("rollbackWeight    = " ^ Int.toString (!rollbackWeight) ^ "\n");
           transactionCount := 0;
           rollbackCount := 0;
           rollbackWeight := 0)

      structure String = Silly.String      
      
      structure X = Indexing
      structure IV = IndexSym
      structure D = CvclDirect

      fun varmapToString () = "()"

      structure Cookie :> sig
                  eqtype cookie
                  val fresh : unit -> cookie
                  val rollback : cookie -> 'a -> (unit -> 'a (* replay function; called iff `cookie' is not current *)) -> 'a
                  val toString : cookie -> string
                  val reset : unit -> unit
      end
      = struct

        type cookie = int
        val counter : int ref = ref ~1

        fun reset () = counter := ~1
        fun fresh () = (counter := (!counter) + 1; !counter)
        fun rollback cookie curr replayFn =
            if cookie = !counter then
                curr
            else
                replayFn()
        
        fun toString cookie = "*Cookie*" ^ Int.toString cookie
     end

    fun lsplit pfx s k1 k2 =
        if String.isPrefix pfx s then
            k2 (String.extract (s, size pfx, NONE))
        else
            k1 s
    fun rsplit sfx s k1 k2 =
        if String.isSuffix sfx s then
            k2 (String.extract (s, 0, SOME (size s - size sfx)))
        else
            k1 s
    fun rsplitForce sfx s =
        rsplit sfx s (fn _ => raise Option) (fn s => s)

      structure IcsMapper :> sig
                  exception WeirdVar
                  exception MyLittleBrainExploded

                  val reset : unit -> unit

                  val add : IndexSym.sym -> D.vtype -> unit
                  val toIcs : IndexSym.sym -> D.exp
                  val getVtype : IndexSym.sym -> D.vtype
      end
      = struct
        structure IAE = IntStatistEnv
        structure ISAE = IndexSymStatistEnv

        exception WeirdVar
        exception MyLittleBrainExploded

        val toIcs_env : (C.ro C.uchar_obj C.ptr * D.exp * D.vtype) ISAE.env ref = ref (ISAE.empty())

        fun reset () = (toIcs_env := ISAE.empty())

        fun add sym vtype =
            let in case ISAE.get (!toIcs_env) sym of
                       SOME _ => ()
                     | NONE =>
                         let val name = ZString.dupML (IndexSym.toString sym)
                             val exp = D.varCstr name vtype
                             val _ = if !CvclDirect.r_dump then print (IndexSym.toString sym ^ " : " ^ "INT" ^ ";\n")  else ()
                             val _ = toIcs_env := (ISAE.extend (!toIcs_env) [(sym, (name, exp, vtype))])
                         in
                             ()
                         end
            end

        fun get sym =
            let in case ISAE.get (!toIcs_env) sym of
                       NONE => raise Option
                     | SOME stuff => stuff
            end

        fun toIcs sym =
            case get sym of
                (name, exp, vtype) => exp

        fun getVtype sym =
            case get sym of
                (_, exp, vtype) => vtype

      end
               
      type command = D.exp
      
      datatype context =
               CVCL of { session: D.session
                       , history: command list
                       , cookie: Cookie.cookie
                       }

      (* isSuffixList suffix ss
       
           Given a list of strings `ss', determines if  `suffix' is a
           suffix of (String.concat (List.rev ss)).
      *)
      fun isSuffixList suffix ss =
          (   String.isSuffix suffix (String.concat (List.rev ss))  )

      fun cvcl_transact (cvcl as CVCL{session, ...}) inputLine =
          (transactionCount := !transactionCount + 1;
           D.assertFormula inputLine)

      fun replay (cvcl as CVCL{session, history, ...}) =
          let val _ = D.reset ()
              fun aux [] = cvcl
                | aux (h1 :: history) =
                    let val _ = D.assertFormula h1
                        val _ = rollbackWeight := !rollbackWeight + 1
                    in
                        aux history
                    end
          in
              rollbackCount := !rollbackCount + 1;
              rollbackWeight := !rollbackWeight + 1;
              aux history
          end

      structure Context = struct

          fun fromSession session =
              raise Option
(*              CVCL{session= session,
                   history= [],
                   cookie= Cookie.fresh()} *)

          fun new location =
              let val _ = D.kill_all()
                  val session = D.new_session()
              in
                  SOME (CVCL{session= session,
                             history= [],
                             cookie= Cookie.fresh()})
              end
      end
      
      datatype assertresult =
          Unsat
        | Ok of context * (Indexing.exp * Indexing.exp) list
        | Valid

    fun resultize ics result f1 f2 =
        case result of
            Unsat => f1 ics
          | Valid => f2 ics
          | Ok(ics, _) => f2 ics

    fun recorded_cvcl_assert (cvcl as CVCL{session, history, cookie}) inputLine =
        let val result = cvcl_transact cvcl inputLine
            val cvcl = CVCL{session= session, history= inputLine :: history, cookie= Cookie.fresh()}
        in
            (cvcl, result)
        end
    
    fun save (cvcl as CVCL{session= session, history= history, cookie= cookie}) =
        let in
            (cvcl,
             fn cvcl' =>
                   let in
                       cvcl
                   end)
        end

    fun saveForward ics =
        let val (ics, restorer) = save ics
        in
            ics
        end

      fun infixBinaryOp s =
          case s of
              "+" => SOME D.plus
            | "*" => SOME D.mult
            | "-" => SOME D.minus
            | "/" => SOME D.divide
            | "=" => SOME D.eq
            | "<>" => SOME D.neq
            | "<" => SOME D.lt
            | "<=" => SOME D.le
            | ">" => SOME D.gt
            | ">=" => SOME D.ge
            | _ => NONE

      fun icsexp e =
          let in case e of
              X.Uvar iv => IcsMapper.toIcs iv
            | X.Evar iv => IcsMapper.toIcs iv
            | X.Literal(sort, s) =>
                if (sort = X.getIntSort())  then
                    D.literalInt (valOf (Int.fromString s))
                else
                    raise Option
        | X.App(f, X.Tuple [exp1, exp2]) =>
                let val fString = IndexSym.toShortString f
                in
                        let in case infixBinaryOp fString of
                                   SOME f => f(icsexp exp1, icsexp exp2)
                                 | NONE => raise Option
                        end
                end
(*        | X.App(f, X.Tuple exps) => 
              let val fString = IndexSym.toShortString f
              in
                  fString << "(" << comma (map icsexp exps) >> ")"
              end
*)
        | X.App(f, exp) => 
              let val fString = IndexSym.toShortString f
                  val f = case fString of
                              "~" => D.uminus
              in
                  f (icsexp exp)
              end
        | X.Nil _ => raise Option
        | X.True => D.literalBool(true)
        | X.False => D.literalBool(false)
    (*    | X.Tuple exps =  *)
    (*    | X.Proj of int * exp *)
(*
      fun ics W =
          case W of
              X.TRUE => []
            | X.AND(W1, W2) => ics W1 @ ics W2
            | X.ALL(a, sort, W0) => ics W0
            | X.EXISTS(a, sort, W0) => ics W0
            | X.IMPLIES(W1, W2) => mkSaveRestore ([mkAssert W1] @ ics W2)
            | X.EQ(e1, e2) => icsexp e1 << " = " << icsexp e2
*)
          end

    fun icssimplify exp =
        case exp of
             X.App(f, X.Tuple [exp1, exp2 as X.App (g, X.Tuple [exp21, exp22])]) =>
                let val fString = IndexSym.toShortString f
                    val gString = IndexSym.toShortString g
                    val multiplySym = X.lookupFun "*"
                in
                    case (fString, gString) of
                        ("/", "/") => icssimplify (X.App (multiplySym, X.Tuple[exp1, X.App (g, X.Tuple [exp22, exp21])]))
                      | (_, _) => X.App (f, X.Tuple [icssimplify exp1, icssimplify exp2])
                end
           | X.App(f, exp) => X.App(f, icssimplify exp)
           | X.Tuple exps => X.Tuple (map icssimplify exps)
           | exp => exp

    val icsexp = icsexp o icssimplify

    fun icspred_simple (predString, exp) =
        let in case exp of
                X.Tuple [] => raise Option
              | X.Tuple [first, second] =>
                  let val f = case predString of
                                  "=" => D.eq
                                | "<>" => D.neq
                                | "<" => D.lt
                                | "<=" => D.le
                                | ">" => D.gt
                                | ">=" => D.ge
                  in
                      f(icsexp first, icsexp second)
                  end
              | one =>
                  let val f = case predString of
                                  _ => raise Option
                  in
                      f (icsexp exp)
                  end
        end

    datatype stultification_style =
             CheckingValidity
           | Asserting

    (* stultify: Stultifies a predicate.  <, <=, >, >= must be "stultified"
     due to ICS thinking that the integers are the rationals. 
     When `CheckingValidity', try to WEAKEN the predicate;
      when `Asserting', try to STRENGTHEN the predicate.

     How is this done? Some propositions are equivalent/of the same strength
     over the integers, but not over the rationals.  For example, 
            x >= 0   iff   x + 1 > 0       if x is over the integers,
     but
           x >= 0   is not implied by   x + 1 > 0    if x is over the rationals (consider x = -1/2).
     Therefore, we can weaken x >= 0 to x + 1 > 0, or strengthen x + 1 > 0 to x >= 0,
     depending on the `sense' argument.
     *)
    fun stultify (sense : stultification_style) (pred, exp) =
        let val plusFun = X.lookupFun "+"
            val minusFun = X.lookupFun "-"
            val intSort = X.getIntSort()
            val one = X.Literal(intSort, "1")
            fun plusOne e = X.App(plusFun, X.Tuple[e, one])
        in
            case (sense, IndexSym.toShortString pred, exp) of
                (Asserting (*strengthen*), ">", X.Tuple[e1, e2]) =>
                (">=", X.Tuple[e1,
                               plusOne e2])
(*              | (CheckingValidity (*weaken*), ">=", X.Tuple[e1, e2]) =>
                (">", X.Tuple[plusOne e1,
                              e2])
*)            | (Asserting (*strengthen*), "<", X.Tuple[e1, e2]) =>
                ("<=", X.Tuple[plusOne e1,
                               e2])
(*              | (CheckingValidity (*weaken*), "<=", X.Tuple[e1, e2]) =>
                ("<", X.Tuple[e1,
                              plusOne e2])
*)
              | (sense, predString, exp) => (predString, exp)
        end

    fun icspred  sense (pred, exp) =
        icspred_simple (stultify sense (pred, exp))
        

    fun getEqs (ics as CVCL{session= session, ...}) varMaker =
        [] (* XXX *)

     fun rollback (cvcl as CVCL{session, history, cookie}) =
         let val _ = replay cvcl
         in
             CVCL{session= session, history= history, cookie= Cookie.fresh()}
         end

     fun reaffirm (cvcl as CVCL{cookie, ...}) =
         Cookie.rollback cookie cvcl (fn () => rollback cvcl)

      fun assertCore cvcl exp =
          let val cvcl = reaffirm cvcl
              val (cvclX, empty_result) = recorded_cvcl_assert cvcl (exp)
              val result = D.unsafeQuery (D.literalBool(false))
(*              val _ = dprint (fn () => "assertCore > >    " ^ D.queryResultToString result ^ " < <") *)
          in
              case result of
                  D.Valid =>  (* Falsehood is entailed: assertion led to inconsistency. *)
                                  (dprint (fn () => "assertCore -- inconsistent");
                                       rollback cvcl (* not cvclX: must not include contradictory assertion *); Unsat)
                | D.Invalid =>
                   (dprint (fn () => "assertCore -- consistent");
                     Ok (saveForward cvclX, []))
          end

     fun constraintize e = case e of
       X.App(p, arg) => X.PRED(p, arg)
      | X.Evar evar => X.TRUE (* !! *)
      | X.Uvar uvar => X.TRUE (* !! *)
      | X.Nil sym => raise Option
      | X.True => X.TRUE
      | X.False => raise Option
      | X.Literal _ => raise Option
      | X.Tuple _ => raise Option
      | X.Proj _ => raise Option

     fun negate_constraintize e =
         case constraintize e of
             X.PRED(p, arg) =>
                 let in case X.getSyminfo p of
                         SOME (X.IFun[{complement= NONE, ...}]) => X.TRUE
                       | SOME (X.IFun[{complement= SOME complement, ...}]) =>
                             (dprint (fn () => "Noticing complement: `" ^ IndexSym.toShortString complement ^ "' ");
                              X.PRED(complement, arg))
                 end
           | X.TRUE => X.TRUE

     fun declare (ics as CVCL{session= session, history= history, cookie= cookie}, (a, sort)) =
         case sort of
             X.Base sortname =>
             let in if sortname = X.getIntSort() then
                 let val _ = IcsMapper.add a (D.intType())
(*XXX*)
                         (* Need not be recorded, because CVCL (like ICS) remembers type declarations across RESETs. *)
                 in 
                     Valid
                 end
                    else if sortname = X.getBoolSort() then
                        let val _ = IcsMapper.add a (D.boolType())
                        in
                            Valid
                        end
                    else if sortname = X.getDimSort() then
                       Valid
                    else
                        raise Option (* unknown base sort name *)
             end
           | X.Product _ => Valid  (* XXX *)
           | X.List sort0 => Valid   (* XXX ?  can't figure out how to declare S-exprs in ICS... *)
           | X.Subset(sort0, a0, P) =>
                 let fun ggg ics =
                     let val P = X.Constraint.subst [(a0, X.Uvar a)] P
                     in
                         assert (ics, P, fn _ => raise Option)
                     end
                 in
                     resultize ics (declare (ics, (a, sort0))) (fn _ => Unsat) ggg
                 end

     and assert (ics, W, varMaker) =
          let val _ = dprint (fn () => "Cvcl.assert:  " ^ X.Constraint.toString W ^ "\n")
          in
              case W of
                  X.TRUE => Valid
                | X.AND(W1, W2) =>
                      let in case assert (ics, W1, varMaker) of
                           Unsat => Unsat
                         | Valid => assert(ics, W2, varMaker)
                         | Ok(ics, bindings) =>
                               let in case assert(ics, W2, varMaker) of
                                    Unsat => Unsat
                                  | Valid => Ok(ics, bindings)
                                  | Ok(ics, bindings2) => Ok(saveForward ics, bindings @ bindings2)
                               end
                      end
                | X.ALL(a, sort, W0) =>
                      let in case declare (ics, (a, sort)) of
                          Unsat => Unsat
                        | Valid => assert(ics, W0, varMaker)
                        | Ok(ics, bindings) => assert(ics, W0, varMaker)
                      end
                | X.EXISTS(a, sort, W0) =>
                      let in case declare (ics, (a, sort)) of
                          Unsat => Unsat
                        | Valid => assert(ics, W0, varMaker)
                        | Ok(ics, bindings) => assert(ics, W0, varMaker)
                      end
                | X.EQ(X.Product sorts, X.Tuple es1, X.Tuple es2) =>
                      assert(ics, foldl X.mkAND X.TRUE (map X.EQ (MyList.zip3 sorts es1 es2)), varMaker)
                | X.EQ(X.Base basesort, e1, e2) =>
                  if basesort = X.getBoolSort()
                  orelse basesort = X.getIntSort() then 
                      let val s1 = icsexp e1
                          val s2 = icsexp e2
                          val f = if basesort = X.getBoolSort()
                                  then D.iffExpr 
                                  else D.eq
                      in
                          assertCore ics (f(s1, s2))
                      end
                  else
                      raise Option
                | X.PRED(pred, exp) =>
                      let val wholeString = icspred Asserting (pred, exp)
                      in
                          assertCore ics wholeString
                      end
                | X.EQ(sort, e1, e2) => 
                  (print ("Ics unknown X.EQ form: " ^ X.Sort.toString sort ^ ", " ^ X.Exp.toString e1 ^ ", " ^ X.Exp.toString e2 ^ "\n"); raise Option)
          (* | X.IMPLIES ... *)
          end

      val assert = fn arg => (assert arg, [])
          
      fun isValidEq isValidFn (ics, X.Base sortname, (e1, e2)) =
          if e1 = e2 then true
          else
              let val eqf = if sortname = X.getBoolSort() then D.iffExpr else D.eq
                  val s1 = icsexp e1
                  val s2 = icsexp e2
              in
                  replay ics;
                  case D.query (eqf (s1, s2)) of
                      D.Valid => true
                    | D.Invalid => false
              end

      fun isValidPred (ics, (pred, e)) =
          let val _ = replay ics
              val exp = icspred CheckingValidity (pred, e)
          in
              (case D.query exp of
                  D.Valid => true
                | D.Invalid => false)
          end
     
     fun comp m1 [] =
         m1
       | comp m1 ((x, y) :: m2) =
         if x = y then
             comp m1 m2
         else
             let in case Assoc.getOpt m1 y of
                 NONE => comp ((x, y) :: m1) m2
               | SOME z => comp ((x, z) :: m1) m2
             end

    fun glork cvcl =
         "Cvclglork"

    fun reset () =
        (IcsMapper.reset ();
         Cookie.reset ())

    fun knowsSym ics a = true (* XXX *)

end
