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
 signature SOLVER_INTERFACE_YICES_PIPED = sig

    include SOLVER_INTERFACE_CVCL_PIPED

end


structure YicesPiped :> SOLVER_INTERFACE_YICES_PIPED = struct

      val canHandleBooleans = true
      fun negate x = raise Option

      val {dprint, ...} =
          Debug.register {full_name= "YicesPiped",
                          short_name= "YicesPiped"}

      fun getLocation () = SOME (Stardustrc.get (fn Stardustrc.Yices loc => loc))

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

      structure YicesMapper :> sig
                  exception WeirdVar
                  exception MyLittleBrainExploded

                  val reset : unit -> unit

                  val toYices : IndexSym.sym -> string(*YICES name *)
                  val toIV : string(*YICES name, e.g. "la!1{int}" *) -> IndexSym.sym
      end
      = struct
        structure IAE = IntStatistEnv
        structure ISAE = IndexSymStatistEnv

        exception WeirdVar
        exception MyLittleBrainExploded

        val toIV_env : IndexSym.sym IAE.env ref = ref (IAE.empty())
        val toYices_env : int ISAE.env ref = ref (ISAE.empty())

        fun reset () = (toIV_env := IAE.empty();
                        toYices_env := ISAE.empty())

        fun toYices sym =
                    let in case ISAE.get (!toYices_env) sym of
                        NONE => IV.toString sym
                      | SOME n => "la!" ^ Int.toString n ^ "{int}"
                    end

        fun toIV string =
            let
                val k = (fn rest =>
                         let val n = (valOf o Int.fromString o hd) (String.tokens (fn ch => ch = #"{") rest)
                         in
                             case IAE.get (!toIV_env) n of
                                 NONE => (* Add it! *)
                                     let val sym = IndexSym.fresh ("laBang" ^ Int.toString n)
                                         val _ = IAE.extend (!toIV_env) [(n, sym)]
                                         val _ = ISAE.extend (!toYices_env) [(sym, n)]
                                     in
                                         sym
                                     end
                               | SOME sym => sym
                         end)
                val kX = (fn rest => raise WeirdVar)
            in
                lsplit "iv" string
                (fn _ => lsplit "la!" string
                 (fn _ => lsplit "u!" string
                  (fn _ => lsplit "k!" string
                   (fn _ => lsplit "k0!" string
                    (fn _ => raise MyLittleBrainExploded)
                    kX)
                   kX)
                  kX)
                 k)
                (fn rest => (IndexSym.fromInt o valOf o Int.fromString o hd) (String.tokens (fn ch => ch = #"_") rest))
            end
      end
               
      type command = string

      datatype context =
               YICES of { session: Piper.session
                        , history: command list
                        , cookie: Cookie.cookie
                       }

      (* isSuffixList suffix ss
       
           Given a list of strings `ss', determines if  `suffix' is a
           suffix of (String.concat (List.rev ss)).
      *)
      fun isSuffixList suffix ss =
          (   String.isSuffix suffix (String.concat (List.rev ss))  )

      fun yices_transact_session session inputLine = (* inputLine: do not include ";\n" *)
         (transactionCount := !transactionCount + 1;
(*          print ("YYLOUD " ^ inputLine ^ "\n"); *)
          Piper.transact_session session {input= inputLine ^ "\n",
                                             outputSync= (*String.isSuffix*) isSuffixList "\n" })

      fun yices_transact_session_silent session inputLine = (* inputLine: do not include ";\n" *)
         (transactionCount := !transactionCount + 1;
(*          print ("YYQT   " ^ inputLine ^ "\n"); *)
          Piper.transact_yices_silent_session session {input= inputLine ^ "\n"})

      fun yices_transact (yices as YICES{session, ...}) inputLine =
          yices_transact_session session inputLine

      fun yices_transact_silent (yices as YICES{session, ...}) inputLine =
          yices_transact_session_silent session inputLine

      fun replay (yices as YICES{session, history, ...}) =
          let val _ = yices_transact_session_silent session "(pop)"
              val _ = yices_transact_session_silent session "(push)"
              fun aux [] = yices
                | aux (h1 :: history) =
                    let val _(* No result *) = yices_transact_silent yices h1
(*                        val _ = print ("replayed [" ^ h1 ^ "]\n") *)
                        val _ = rollbackWeight := !rollbackWeight + 1
                    in
                        aux history
                    end
          in
(*              print ("replay: history in rev.: [" ^ Separate.list ",,,\n" history ^ "\n]\n"); *)
              rollbackCount := !rollbackCount + 1;
              rollbackWeight := !rollbackWeight + 1;
              aux (List.rev history)
          end

      structure Context = struct

          fun fromSession session =
             (Piper.transact_yices_silent_session session {input="(push)\n"};
              YICES{session= session,
                   history= [],
                   cookie= Cookie.fresh()})

          fun new (SOME location) =
              let val session = case location of
                                  Stardustrc.Local{path}  => Piper.start_local_yices path
(*                                | Stardustrc.Remote{hostname, portNumber} => Piper.start_remote_yices {hostname= hostname,
                                                                             portNumber= portNumber} *)
              in
                Option.map fromSession session
              end
      end
      
      datatype assertresult =
          Unsat
        | Ok of context * (Indexing.exp * Indexing.exp) list
        | Valid

    fun resultize yices result f1 f2 =
        case result of
            Unsat => f1 yices
          | Valid => f2 yices
          | Ok(yices, _) => f2 yices

    fun recorded_yices_transact_loud (yices as YICES{session, history, cookie}) inputLine =
        let val result = yices_transact yices inputLine
            val _ = print ("recorded_yices_transact: adding \"" ^ inputLine ^ "\" to history\n")
            val _ = print ("previous history: \"" ^ Separate.list ";\n " history ^ "\"\n")
            val yices = YICES{session= session, history= inputLine :: history, cookie= Cookie.fresh()}
        in
            (yices, result)
        end

    fun recorded_yices_transact_silent (yices as YICES{session, history, cookie}) inputLine =
        let val _ = yices_transact_silent yices inputLine
            val _ = print ("recorded_yices_transact: adding \"" ^ inputLine ^ "\" to history\n")
            val _ = print ("previous history: \"" ^ Separate.list ";\n " history ^ "\"\n")
            val yices = YICES{session= session, history= inputLine :: history, cookie= Cookie.fresh()}
        in
          yices
        end

    fun norepeat_kludge_recorded_yices_transact_silent (yices as YICES{history, ...}) inputLine =
        if MyList.contains inputLine history then
          yices
        else
          recorded_yices_transact_silent yices inputLine
    
    fun save (yices as YICES{session= session, history= history, cookie= cookie}) =
        let in
            (yices,
             fn yices' =>
                   let in
                       yices
                   end)
        end

    fun saveForward yices =
        let val (yices, restorer) = save yices
        in
            yices
        end

(*      fun mkSaveRestore stuff =
            let val qs = YicesStateName.toString (YicesStateName.fresh())
            in
                         ["save " ^ qs ^ "."]
                         @ stuff
                         @ ["restore " ^ qs ^ "."]
            end
*)

      fun infixBinaryOp s = false
(*          case s of
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
*)

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
      fun space ws = separator " " ws

      fun yicesexp e =
          let in
          case e of
              X.Uvar iv => just (YicesMapper.toYices iv)
            | X.Evar iv => just (YicesMapper.toYices iv)
            | X.Literal(sort, s) =>
              if (sort = X.getIntSort()) andalso (String.sub(s, 0) = #"~") then
                  "-" << just (String.extract(s, 1, NONE))
              else
                  just s
        | X.App(f, X.Tuple [exp1, exp2]) =>
                let val fString = IndexSym.toShortString f
                in
                    if fString = "/" then
                        "(/ " << (yicesexp exp1 @@ (" " << yicesexp exp2 >> ")"))    (* Wrong.  Yices allows division only for k1/k2 where k1, k2 are integer constants. *)
                    else
                        ("(" << fString << " " << yicesexp exp1 >> " ") @@ (yicesexp exp2 >> ")")
                end
        | X.App(f, X.Tuple exps) => 
              let val fString = IndexSym.toShortString f
              in
                  "(" << fString << " " << space (map yicesexp exps) >> ")"
              end
        | X.App(f, exp) => 
              let val fString = IndexSym.toShortString f
              in
                  fString << "(" << yicesexp exp >> ")"
              end
        | X.Nil _ => just "nil"
        | X.True => just "true"
        | X.False => just "false"
    (*    | X.Tuple exps =  *)
    (*    | X.Proj of int * exp *)
(*
      fun yices W =
          case W of
              X.TRUE => []
            | X.AND(W1, W2) => yices W1 @ yices W2
            | X.ALL(a, sort, W0) => yices W0
            | X.EXISTS(a, sort, W0) => yices W0
            | X.IMPLIES(W1, W2) => mkSaveRestore ([mkAssert W1] @ yices W2)
            | X.EQ(e1, e2) => yicesexp e1 << " = " << yicesexp e2
*)
          end

    fun yicessimplify exp =
        case exp of
             X.App(f, X.Tuple [exp1, exp2 as X.App (g, X.Tuple [exp21, exp22])]) =>
                let val fString = IndexSym.toShortString f
                    val gString = IndexSym.toShortString g
                    val multiplySym = X.lookupFun "*"
                in
                    case (fString, gString) of
                        ("/", "/") => yicessimplify (X.App (multiplySym, X.Tuple[exp1, X.App (g, X.Tuple [exp22, exp21])]))
                      | (_, _) => X.App (f, X.Tuple [yicessimplify exp1, yicessimplify exp2])
                end
           | X.App(f, exp) => X.App(f, yicessimplify exp)
           | X.Tuple exps => X.Tuple (map yicessimplify exps)
           | exp => exp

    val yicesexp = yicesexp o yicessimplify

    fun yicespred_simple (predString, exp) =
        let val predString =
            case predString of
                "<>" => "/=" (* CVC Lite not-equals *)
              | _ => predString
        in
            case exp of
                X.Tuple [] => just ("(" ^ predString ^ ")")
              | X.Tuple [first, second] => ("(" << predString << (" " << yicesexp first)) @@ (" " << yicesexp second >> ")")
              | one => predString << " " << yicesexp one
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

    fun yicespred  sense (pred, exp) =
        yicespred_simple (stultify sense (pred, exp))
        

    fun getEqs (yices as YICES{session= session, ...}) varMaker =
        [] (* XXX *)

     fun rollback (yices as YICES{session, history, cookie}) =
         let val _ = replay yices
         in
             YICES{session= session, history= history, cookie= Cookie.fresh()}
         end

     fun reaffirm (yices as YICES{cookie, ...}) =
         Cookie.rollback cookie yices (fn () => rollback yices)
      
     fun assertCoreString yices string =
         let val yices = reaffirm yices
             val yicesX = recorded_yices_transact_silent yices ("(assert " ^ string ^ ")" (*; QUERY(FALSE)"*) )
             val result = yices_transact yicesX ("(check)")  (* empty_result *)
             val _ = dprint (fn () => "assertCore > >    " ^ result ^ "\n < <\n")
         in
             if String.isPrefix "unsat" result then  (* Falsehood is entailed: assertion led to inconsistency. *)
                 (rollback yices (* not yicesX: must not include contradictory assertion *); Unsat)
             else if String.isPrefix "sat" result then
                 Ok (saveForward yicesX, [])
             else
                 (print ("assertCoreString: unknown result: ``" ^ result ^ "''\n");
                  raise Option)
         end

     fun assertCore yices willow =
         assertCoreString yices (willowToString willow)

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

     fun declare (yices as YICES{session= session, history= history, cookie= cookie}, (a, sort)) =
         let val yices = replay yices
         in
             case sort of
                 X.Base sortname =>
                   let fun define sortname =
                           let val yices' = norepeat_kludge_recorded_yices_transact_silent yices ("(define " ^ IV.toString a ^ "::" ^ sortname ^ ")")
                           in 
                             Ok(yices', [])
                           end
                   in
                       if sortname = X.getIntSort() then define "int"
                       else if sortname = X.getBoolSort() then define "bool"
                       else if sortname = X.getDimSort() then Valid
                       else raise Option (* unknown base sort name *)
                   end
               | X.Product _ => Valid  (* XXX *)
               | X.List sort0 => Valid   (* XXX ?  how to declare S-exprs? *)
               | X.Subset (sort0, a0, P) =>
                     let fun ggg yices =
                         let val P = X.Constraint.subst [(a0, X.Uvar a)] P
                         in
                             assert (yices, P, fn _ => raise Option)
                         end
                     in
                         resultize yices (declare (yices, (a, sort0))) (fn _ => Unsat) ggg
                     end
         end

     and assert (yices, W, varMaker) =
          let val _ = dprint (fn () => "Yices.assert:  " ^ X.Constraint.toString W ^ "\n")
          in
              case W of
                  X.TRUE => Valid
                | X.AND(W1, W2) =>
                      let in case assert (yices, W1, varMaker) of
                           Unsat => Unsat
                         | Valid => assert(yices, W2, varMaker)
                         | Ok(yices, bindings) =>
                               let in case assert(yices, W2, varMaker) of
                                    Unsat => Unsat
                                  | Valid => Ok(yices, bindings)
                                  | Ok(yices, bindings2) => Ok(saveForward yices, bindings @ bindings2)
                               end
                      end
                | X.ALL(a, sort, W0) =>
                      let in case declare (yices, (a, sort)) of
                          Unsat => Unsat
                        | Valid => assert(yices, W0, varMaker)
                        | Ok(yices, bindings) => assert(yices, W0, varMaker)
                      end
                | X.EXISTS(a, sort, W0) =>
                      let in case declare (yices, (a, sort)) of
                          Unsat => Unsat
                        | Valid => assert(yices, W0, varMaker)
                        | Ok(yices, bindings) => assert(yices, W0, varMaker)
                      end
                | X.EQ(X.Product sorts, X.Tuple es1, X.Tuple es2) =>
                      assert(yices, foldl X.AND X.TRUE (map X.EQ (MyList.zip3 sorts es1 es2)), varMaker)
                | X.EQ(X.Base basesort, e1, e2) =>
                  if basesort = X.getBoolSort()
                  orelse basesort = X.getIntSort() then 
                      let val s1 = yicesexp e1
                          val s2 = yicesexp e2
                      in
                          assertCore yices ("(= " << s1 @@ just " " @@ s2 >> ")")
                      end
                  else
                      raise Option
                | X.PRED(pred, exp) =>
                      let val wholeString = yicespred Asserting (pred, exp)
                      in
                          assertCore yices wholeString
                      end
                | X.EQ(sort, e1, e2) => 
                  (print ("Yices unknown X.EQ form: " ^ X.Sort.toString sort ^ ", " ^ X.Exp.toString e1 ^ ", " ^ X.Exp.toString e2 ^ "\n"); raise Option)
          (* | X.IMPLIES ... *)
          end
      
      fun isValidString (yices, willow) =
          let 
              val string = willowToString willow
              val yices = reaffirm yices
              val _ = yices_transact_silent yices ("(assert " ^ string ^ ")")   (* Not recorded.  ??? *)
              val result = yices_transact yices "(check)"   (* Not recorded.  ??? *)
              val _ = dprint (fn () => "isValidString > > \n" ^ result ^ "\n < <")
          in
              if String.isPrefix "unsat" result then
                  false
              else if String.isPrefix "sat" result then
                  true
              else
                  raise Option   (* WTF? *)
          end

      val assert = fn arg => (assert arg, [])
          
      fun isValidEq isValidFn (yices, X.Base sortname, (e1, e2)) =
          if e1 = e2 then true
          else
              let
                  val s1 = yicesexp e1
                  val s2 = yicesexp e2
              in
                  isValidString (yices, ("(= " << s1 >> " ") @@ s2 >> ")")
              end

      fun isValidPred (yices, (pred, e)) =
          let val string = yicespred CheckingValidity (pred, e)
              val _ = dprint (fn () => "isValidPred       " ^ willowToString string)
          in
              isValidString(yices, string)
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

    fun glork yices =
         "Yicesglork"

    fun knowsSym ics a = true (* XXX *)

    fun reset () =
        (YicesMapper.reset ();
         Cookie.reset ())

end (* structure YicesPiped *)
