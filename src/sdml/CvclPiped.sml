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
signature SOLVER_INTERFACE_CVCL = sig

    include SOLVER_INTERFACE

    val printResetCounts : unit -> unit
end


signature SOLVER_INTERFACE_CVCL_PIPED = sig

    include SOLVER_INTERFACE_CVCL

end

structure CvclPiped :> SOLVER_INTERFACE_CVCL_PIPED = struct

      val canHandleBooleans = true
      fun negate x = raise Option

      val {dprint, ... (*dprnt  Thou shalt not use dprnt*)} =
          Debug.register {full_name= "CvclPiped",
                          short_name= "CvclPiped"}

      fun getLocation () = SOME (Stardustrc.get (fn Stardustrc.Cvc3 loc => loc))
      
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
                  val reset : unit -> unit

                  val toIcs : IndexSym.sym -> string(*ICS name *)
      end
    =
    struct

      fun reset () = ()
      fun toIcs sym = IV.toString sym
    end
               
    type command = string

    datatype context =
               CVCL of { session: Piper.session
                        , history: command list
                        , cookie: Cookie.cookie
                       }

    (* isSuffixList suffix ss

         Given a list of strings `ss', determines if  `suffix' is a
         suffix of (String.concat (List.rev ss)).
    *)
    fun isSuffixList suffix ss =
        (   String.isSuffix suffix (String.concat (List.rev ss))  )

    fun cvcl_transact_session session inputLine = (* inputLine: do not include ";\n" *)
       (transactionCount := !transactionCount + 1;
       let fun wasteTime 0 = ()
             | wasteTime n = let val result = Piper.transact_session session {input= "ASSERT(TRUE);\n",
                                                        outputSync = isSuffixList "CVC> "}
       in wasteTime (n-1)  end
       val _ = wasteTime 0
    in
           Piper.transact_session session {input= inputLine ^ ";\n",
                                           outputSync= (*String.isSuffix*) isSuffixList "CVC> " }
       end)

    fun cvcl_transact (cvcl as CVCL{session, ...}) inputLine =
        cvcl_transact_session session inputLine

    fun replay (cvcl as CVCL{session, history, ...}) =
        let val _ = cvcl_transact_session session "POP"
            val _ = cvcl_transact_session session "PUSH"
            fun aux [] = cvcl
              | aux (h1 :: history) =
                  let val _(* Throw away string result *) = cvcl_transact cvcl h1
                      val _ = rollbackWeight := !rollbackWeight + 1
                  in
                      aux history
                  end
        in
(*              print ("replay: history: [" ^ Separate.list ",,,\n" history ^ "\n]\n"); *)
            rollbackCount := !rollbackCount + 1;
            rollbackWeight := !rollbackWeight + 1;
            aux history
        end

    structure Context = struct

        fun fromSession session =
           (Piper.transact_session session {input="PUSH;\n", outputSync = isSuffixList "CVC> "};
            CVCL{session= session,
                 history= [],
                 cookie= Cookie.fresh()})

        fun new (SOME location) =
            let val session = case location of
                                Stardustrc.Local{path}  => Piper.start_local_cvcl path
                              | Stardustrc.Remote{hostname, portNumber} => Piper.start_remote_cvcl {hostname= hostname,
                                                                           portNumber= portNumber}
            in
                Option.map fromSession session
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

  fun recorded_cvcl_transact (cvcl as CVCL{session, history, cookie}) inputLine =
      let val result = cvcl_transact cvcl inputLine
(*            val _ = print ("recorded_cvcl_transact: adding \"" ^ inputLine ^ "\" to history\n")
          val _ = print ("previous history: \"" ^ Separate.list ";\\n " history ^ "\"\n") *)
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

    fun mkValid s = "valid " ^ s ^ "."
    fun mkAssert s = "assert " ^ s ^ "."
(*      fun mkSaveRestore stuff =
          let val qs = IcsStateName.toString (IcsStateName.fresh())
          in
                       ["save " ^ qs ^ "."]
                       @ stuff
                       @ ["restore " ^ qs ^ "."]
          end
*)

    fun infixBinaryOp s =
        case s of
            "+" => true
          | "*" => true
          | "-" => true
          | "/" => true
          | "<" => true
          | "<=" => true
          | "=" => true
          | ">=" => true
          | ">" => true
          | "<=>" => true
          | "/=" => true
          | "<>" => true
          | _ => false

    datatype willow =
             Leaf of string
           | Branch of willow * willow

    fun << (s1 : string, w) = Branch(Leaf s1, w)
    infixr 5 <<

    fun >> (w, s2 : string) = Branch(w, Leaf s2)
    infix 4 >>

    fun @@ (w1, w2) = Branch(w1, w2)
    infix 3 @@

    val $$ = Leaf ""
    fun just s = Leaf s

    fun willowToList (Leaf s) = [s]
      | willowToList (Branch(w1, w2)) = (willowToList w1) @ (willowToList w2)

    val willowToString = String.concat o willowToList

    fun separatorString sep [] = $$
      | separatorString sep (s :: ss) = s << separatorString sep ss
    fun commaString ss = separatorString "," ss

    fun separator sep [] = $$
      | separator sep [w] = w
      | separator sep (w :: ws) = (w >> sep) @@ (separator sep ws)
    fun comma ws = separator "," ws

    fun icsexp e =
        let in
        case e of
            X.Uvar iv => just (IcsMapper.toIcs iv)
          | X.Evar iv => just (IcsMapper.toIcs iv)
          | X.Literal(sort, s) =>
            if (sort = X.getIntSort()) andalso (String.sub(s, 0) = #"~") then
                "-" << just (String.extract(s, 1, NONE))
            else
                just s
      | X.App(f, X.Tuple [exp1, exp2]) =>
              let val fString = IndexSym.toShortString f
              in
                  if fString = "/" then
                      "(" << (icsexp exp1 @@ ("/" << icsexp exp2 >> ")"))    (* Wrong.  ICS allows division only for k1/k2 where k1, k2 are integer constants. *)
                  else if infixBinaryOp fString then
                      "(" << (icsexp exp1 >> ") " >> fString >> " (") @@ (icsexp exp2 >> ")")
                       else
                           (fString << "(" << icsexp exp1 >> ", ") @@ (icsexp exp2 >> ")")
              end
      | X.App(f, X.Tuple exps) => 
            let val fString = IndexSym.toShortString f
            in
                fString << "(" << comma (map icsexp exps) >> ")"
            end
      | X.App(f, exp) => 
            let val fString = IndexSym.toShortString f
            in
                fString << "(" << icsexp exp >> ")"
            end
      | X.Nil _ => just "nil"
      | X.True => just "TRUE"
      | X.False => just "FALSE"
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
      let val predString =
          case predString of
              "<>" => "/=" (* CVC Lite not-equals *)
            | _ => predString
      in
          case exp of
              X.Tuple [] => predString << just "()"
            | X.Tuple [first, second] => ("(" << icsexp first >> ") " >> predString) @@ (" (" << icsexp second >> ")")
            | one => predString << " " << icsexp one
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

   fun rollback (_(*unused*), cvcl as CVCL{session, history, cookie}) =
       let val _ = replay cvcl
       in
           CVCL{session= session, history= history, cookie= Cookie.fresh()}
       end

   fun reaffirm (cvcl as CVCL{cookie, ...}) =
       Cookie.rollback cookie cvcl (fn () => rollback ((*XXX*)cvcl, cvcl))

    fun assertCoreString cvcl string =
        let val cvcl = reaffirm cvcl
            val (cvclX, empty_result) = recorded_cvcl_transact cvcl ("ASSERT(" ^ string ^ ")" (*; QUERY(FALSE)"*) )
            val result = cvcl_transact cvclX ("QUERY(FALSE)")  (* empty_result *)
            val _ = dprint (fn () => "assertCore > >    " ^ result ^ "\n < <\n")
        in
            if String.isPrefix "Valid." result then  (* Falsehood is entailed: assertion led to inconsistency. *)
                (rollback (cvclX, cvcl) (* not cvclX: must not include contradictory assertion *); Unsat)
            else if String.isPrefix "InValid." result then
                Ok (saveForward cvclX, [])
            else if String.isPrefix "Invalid." result then   (* recent versions of CVC Lite don't use interCaps here *)
                Ok (saveForward cvclX, [])
            else
                raise Option   (* ???? *)
        end

   fun assertCore ics willow =
       assertCoreString ics (willowToString willow)

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
               let val basesortname = "INT"  (* XXX *)
(*                     val (cvcl, result) = recorded_cvcl_transact ics (IV.toString a ^ " : " ^ basesortname) *)
                   val result = cvcl_transact ics (IV.toString a ^ " : " ^ basesortname)
                       (* Need not be recorded, because CVC Lite (like ICS) remembers type declarations across RESETs. *)
                       (* ---CVC3 doesn't remember type declarations across RESETs, but does across POPs... *)
               in 
                   (* Ok(cvcl, []) *) Valid
               end
                  else if sortname = X.getBoolSort() then
(*                     let val (cvcl, result) = recorded_cvcl_transact ics (IV.toString a ^ " : " ^ "BOOLEAN")
                   in 
                       Ok(cvcl, [])
                   end
*)
                   let val result = cvcl_transact ics (IV.toString a ^ " : " ^ "BOOLEAN")
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
        let val _ = dprint (fn () => "CvclPiped.assert:  " ^ X.Constraint.toString W ^ "\n")
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
                    assert(ics, foldl X.AND X.TRUE (map X.EQ (MyList.zip3 (sorts, es1, es2))), varMaker)
              | X.EQ(X.Base basesort, e1, e2) =>
                if basesort = X.getBoolSort()
                orelse basesort = X.getIntSort() then 
                    let val s1 = icsexp e1
                        val s2 = icsexp e2
                        val f = if basesort = X.getBoolSort()
                                then " <=> "
                                else " = "
                    in
                        assertCore ics (s1 @@ (just f) @@ s2)
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

    fun isValidString (cvcl, willow) =
        let 
            val string = willowToString willow
            val cvcl = reaffirm cvcl
            val result = cvcl_transact cvcl ("QUERY(" ^ string ^ ")")   (* Not recorded.  ??? *)
            val _ = dprint (fn () => "isValidString > > \n" ^ result ^ "\n < <")
        in
            if String.isPrefix "Invalid." result then  (* recent versions of CVC Lite *)
                false
            else if String.isPrefix "Valid." result then
                true
            else
                 raise Option   (* WTF? *)
        end

    val assert = fn arg => (assert arg, [])

    fun isValidEq isValidFn (ics, X.Base sortname, (e1, e2)) =
        if e1 = e2 then true
        else
            let
                val s1 = icsexp e1
                val s2 = icsexp e2
            in
                if sortname = X.getBoolSort() then
                    isValidString (ics, (s1 >> " <=> ") @@ s2)
                else
                    isValidString (ics, (s1 >> " = ") @@ s2)
            end

    fun isValidPred (ics, (pred, e)) =
        let val string = icspred CheckingValidity (pred, e)
            val _ = dprint (fn () => "isValidPred       " ^ willowToString string)
        in
            isValidString(ics, string)
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

    type point = int
    fun push context = (context, ~1)
    fun popto (context, _) = context

    fun knowsSym ics a = true (* XXX *)

end
