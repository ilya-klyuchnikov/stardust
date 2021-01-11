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
(*
 Reference implementation:

 - Maintain history of ASSERTs

 - Before every ASSERT:    (.assert)
        PUSH
        replay history
        do new ASSERT (and add to history)
        POP

 - Before every QUERY:     (.isValidEq, .isValidPred)
        PUSH
        replay history
        do QUERY
        POP
*)

signature SOLVER_INTERFACE_CVC4_PIPED = sig

    include SOLVER_INTERFACE

    val printResetCounts : unit -> unit

    val r_redundant_assertion_count : int ref

end

structure Cvc4Piped :> SOLVER_INTERFACE_CVC4_PIPED = struct

    val r_redundant_assertion_count = ref 0

    val canHandleBooleans = true
    fun negate x = raise Option
    
    val {dprint, ... (*dprnt  Thou shalt not use dprnt*)} =
        Debug.register {full_name= "Cvc4Piped",
                        short_name= "Cvc4Piped"}

    val prompt = "CVC4> "
    
    fun getLocation () = SOME (Stardustrc.get_with (Stardustrc.Local {path= "/usr/local/bin/cvc4"})
                                                   (fn Stardustrc.Cvc4 loc => loc))

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
            val set : cookie -> unit
            val toString : cookie -> string
            val reset : unit -> unit
    end
    =
    struct

        type cookie = int
        val counter : int ref = ref ~1

        val state : int ref = ref ~1

        fun reset () = (counter := ~1; state := !counter);
        fun fresh () = (counter := (!counter) + 1;
                        state := !counter;
                        !counter)

        fun rollback cookie curr replayFn =
            if cookie = !state then
                curr
            else
                replayFn()

        fun set cookie =
            state := cookie

        fun toString cookie = "*Cookie*" ^ Int.toString cookie
    end
    
    structure IcsMapper :> sig
          val reset : unit -> unit
          
          val mapped : IndexSym.sym -> bool
          val known : unit -> IndexSym.sym list  (* = {iv | mapped iv} *)
          val toIcs : IndexSym.sym -> string(*ICS name *)
      end
    =
    struct
    
      val count : int ref = ref 0
      val map : BitArray.array ref = ref (BitArray.bits (0, []))

      fun reset () =
          (count := 0;
           map := BitArray.bits (0, []))
 
      fun mapped sym =
          let val sym = IndexSym.toInt sym
          in
              if sym >= !count then   (* past end of array *)
                  false
              else
                  BitArray.sub (!map, sym)
          end
 
      fun map_extend sym =
          let in
              if sym < !count then
                  ()
              else
                  map := BitArray.extend0 (!map, sym * 2)
            ;
            BitArray.setBit (!map, sym);
            count := Int.max (!count, sym + 1)
          end
      
      fun toIcs sym =
         (map_extend (IndexSym.toInt sym);
          IV.toString sym)

      fun known () =
          List.map IndexSym.fromInt (BitArray.getBits (!map))
    end
    
    datatype command =
           Assert of string   (* ASSERT(string) *)
         | Other of string   (* string *)
    
    fun c2str command = case command of
         Assert string => "Assert(" ^ string ^ ")"
       | Other string => "Other(" ^ string ^ ")"
    
    datatype context =
               CVC4 of { history : command list
                       , cookie : Cookie.cookie
                       }

    fun yammer who (CVC4{history, ...}) =
        ((*print (who ^ ":  history of length " ^ Int.toString (List.length history)
              ^ " that has " ^ Int.toString (List.length (List.filter (fn Push => true | _ => false) history)) ^ " pushes"
              ^ "\n"); *)
         ())
    
    val currSession : Piper.session option ref = ref NONE
    fun getCurrSession() = Option.valOf (!currSession)
    fun setCurrSession (newValue) =
        ( (* should kill old session here *)
        currSession := SOME newValue
        )
    val currDepth : int ref = ref ~9999
    
    fun historyToString history =
        Separate.list ";\n" (List.map c2str history)

    fun CHECK message (cvc4 as CVC4{history, ...}) =
        ()
    
    val current : context option ref = ref NONE
    fun getCurrent() = Option.valOf (!current)
    fun setCurrent (newValue) =
        (yammer "setCurrent FROM " (getCurrent());
         yammer "setCurrent TO " newValue;
         current := SOME newValue
         before
         CHECK "setCurrent" newValue)
        
    fun contextToString (CVC4 {history, cookie}) =
            "CVC4{cookie= "
          ^ Cookie.toString cookie ^ ", "
          ^ "history= " ^ historyToString history
          ^ "}"
    
    (* isSuffixList suffix ss

         Given a list of strings `ss', determines if  `suffix' is a
         suffix of (String.concat (List.rev ss)).
    *)
    fun isSuffixList suffix ss =
        String.isSuffix suffix (String.concat (List.rev ss))
    
    fun cvc4_transact_session inputLine = (* inputLine: do not include ";\n" *)
       (transactionCount := !transactionCount + 1;
        let val session = getCurrSession()
            fun wasteTime 0 = ()
             | wasteTime n = let val result = Piper.transact_session session {input= "ASSERT(TRUE);\n",
                                                                              outputSync = isSuffixList prompt}
                             in wasteTime (n-1)  end
            val _ = wasteTime 0
        in
            Piper.transact_session session {input= inputLine ^ ";\n",
                                            outputSync= (*String.isSuffix*) isSuffixList prompt }
        end)

    fun commandToString command =
        case command of
            Assert string => "ASSERT(" ^ string ^ ")"
          | Other string => string

    fun eternal_cvc4_transact cvc4 command =
       let val result = 
                   cvc4_transact_session (commandToString command)
       in
           result
       end

(*
    fun eternal_cvc4_transact_list (cvc4 as CVC4{depth, ...}) commands =
        cvc4_transact_session depth (Separate.list "; " (List.map commandToString commands))*)


   (* replay (cvc4', cvc4):
         move from cvc4', the current context reflected in CVC4's internal state, to the context cvc4 *)
    fun replay (cvc4' as CVC4{history= history', ...},
                cvc4 as CVC4{history= history, ...}) =
        let val _ = yammer "replay cvc4'" cvc4'
            val _ = yammer "replay cvc4 " cvc4
            val rev_history' = List.rev history'
            val rev_history = List.rev history

(*
            val _ = print "REPLAY\n"
            val _ = print "cvc4': \n"
            val _ = print (contextToString cvc4')
            val _ = print "\ncvc4: \n"
            val _ = print (contextToString cvc4 ^ "\n")
*)            
            val cvc4 = ()

            fun transact cvc command =
                let val _ = eternal_cvc4_transact cvc command
                in
                    ()
                end

            val _ = transact cvc4' (Other "POP;PUSH")
            
            fun redo commands =
                let fun glob [] = []
                      | glob [c] = [c]
                      | glob (Assert ass1 :: rest) = (Assert ass1) :: (glob rest)
(*                      | glob (Assert ass1 :: Assert ass2 :: rest) = 
                           (print "\\";
                            Assert("(" ^ ass1 ^") AND (" ^ ass2 ^ ")") :: glob rest
                            )
*)
                      | glob (c :: rest) = c :: (glob rest)

                in
                    List.app (fn command => 
                                                 let
                                                     (*val _ = print ("-redo- " ^ c2str command ^ "\n") *)
                                                 in
                                                     transact cvc4' command
                                                 end)
                             (glob commands)
                end

        in
(*              print ("replay: history: [" ^ Separate.list ",,,\n" history ^ "\n]\n"); *)
            rollbackCount := !rollbackCount + 1;
            rollbackWeight := !rollbackWeight + 1;

            redo rev_history

            before
            (Piper.echo (fn () => "% replay ENDS\n")
(*           ;  if !currDepth <> depth then
                 print ("REPLAY WARNING (exit): !currDepth <> depth\n")
             else ();
*)
            )
(*            before
            print "aux: END OF RUN\n"
*)
        end

    structure Context = struct

        fun fromSession session =
           (Piper.transact_session session {input="PUSH;\n", outputSync = isSuffixList prompt};
            let val cvc4 = CVC4{history= [],
                                cookie= Cookie.fresh()}
            in
                setCurrSession session;
                currDepth := 1;
                current := SOME cvc4;
                cvc4
            end
           )

        fun new (SOME location) =
            let val session = case location of
                                Stardustrc.Local{path}  => Piper.start_local_cvc4 path
                              | Stardustrc.Remote{hostname, portNumber} => Piper.start_remote_cvc4 {hostname= hostname,
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

  fun update_history (cvc4 as CVC4{history, cookie}) f =
      CVC4{history= f history, cookie= cookie}

  fun recorded_cvc4_transact (cvc4 as CVC4{history, cookie}) inputLine =
      let val _ = CHECK "recorded_cvc4_transact entry cvc4" cvc4
          val _ = CHECK "recorded_cvc4_transact entry getCurrent()" (getCurrent())
          val result = eternal_cvc4_transact cvc4 inputLine
(*            val _ = print ("recorded_cvc4_transact: adding \"" ^ inputLine ^ "\" to history\n")
          val _ = print ("previous history: \"" ^ Separate.list ";\\n " history ^ "\"\n") *)
          val cvc4 = CVC4{history= inputLine :: history,
                          cookie= Cookie.fresh()}
          val _ = setCurrent cvc4
      in
          (cvc4, result)
          before
          (CHECK "recorded_cvc4_transact exit cvc4" cvc4;
            CHECK "recorded_cvc4_transact exit getCurrent()" (getCurrent()))
      end

  fun half_recorded_cvc4_transact (cvc4 as CVC4{history, cookie})
                                         {recorded1,
                                          eternal2} =
      let val _ = eternal_cvc4_transact cvc4 recorded1
          val result = eternal_cvc4_transact cvc4 eternal2
(*            val _ = print ("recorded_cvc4_transact: adding \"" ^ inputLine ^ "\" to history\n")
          val _ = print ("previous history: \"" ^ Separate.list ";\\n " history ^ "\"\n") *)
          val cvc4 = CVC4{history= recorded1 :: history,
                          cookie= Cookie.fresh()}
      in
          (cvc4, result)
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



  fun fix predString = 
      case predString of
          "<>" => "/=" (* CVC Lite not-equals *)
        | _ => predString


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

  fun cvc4exp e =
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
                      "(" << (cvc4exp exp1 @@ ("/" << cvc4exp exp2 >> ")"))    (* Wrong.  ICS allows division only for k1/k2 where k1, k2 are integer constants. *)
                  else if infixBinaryOp fString then
                      "(" << (cvc4exp exp1 >> ") " >> fix fString >> " (") @@ (cvc4exp exp2 >> ")")
                       else
                           (fString << "(" << cvc4exp exp1 >> ", ") @@ (cvc4exp exp2 >> ")")
              end
      | X.App(f, X.Tuple exps) => 
            let val fString = IndexSym.toShortString f
            in
                fString << "(" << comma (map cvc4exp exps) >> ")"
            end
      | X.App(f, exp) => 
            let val fString = IndexSym.toShortString f
            in
                fString << "(" << cvc4exp exp >> ")"
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
          | X.EQ(e1, e2) => cvc4exp e1 << " = " << cvc4exp e2
*)
        end

  fun simplifyconstants exp =
      case exp of
          X.App(f, X.Tuple [X.Literal (sortname, string1), X.Literal (_, string2)]) =>
              if sortname = X.getIntSort() then
                  let val fString = IndexSym.toShortString f
                      val num1 = Option.valOf (Int.fromString string1)
                      val num2 = Option.valOf (Int.fromString string2)
                      fun return n =
                          (X.Literal (sortname, Int.toString n))
                  in
                      case fString of
                          "+" => return (num1 + num2)
                        | "-" => return (num1 - num2)
                        | "*" => return (num1 * num2)
                        | _ => exp
                  end
              else
                  exp
        | X.App(f, X.Tuple [X.App (g, X.Tuple [e0, e1 as X.Literal(sortname1, string1)]),
                           e2 as X.Literal (sortname2, string2)]) =>
              if sortname1 = X.getIntSort() then
                  let val fString = IndexSym.toShortString f
                      val gString = IndexSym.toShortString g
                      val num1 = Option.valOf (Int.fromString string1)
                      val num2 = Option.valOf (Int.fromString string2)
                      fun return n =
                          ((*print "@";*)
                           simplifyconstants (X.App(g, X.Tuple[e0, X.Literal (sortname1, Int.toString n)])))
                  in
                      case (gString, fString) of
                          ("+", "+") => return (num1 + num2)
                        | ("-", "-") => return (num1 + num2)
                        | ("+", "-") => return (num1 - num2)
                        | ("-", "+") => return (num1 - num2)
                        | (_, _) => exp
                  end                  
              else
                  exp
        | X.App(f, X.Tuple [e1, X.Literal (sortname, string2)]) =>
              if sortname = X.getIntSort() then
                  let val fString = IndexSym.toShortString f
                      val num2 = Option.valOf (Int.fromString string2)
                  in
                      case (fString, num2) of
                          ("+", 0) => simplifyconstants e1
                        | ("-", 0) => simplifyconstants e1
                        | ("*", 1) => simplifyconstants e1
                        | _ => exp
                  end
              else
                  exp
        | X.App(f, X.Tuple [X.Literal (sortname, string1), e2]) =>
              if sortname = X.getIntSort() then
                  let val fString = IndexSym.toShortString f
                      val num1 = Option.valOf (Int.fromString string1)
                  in
                      case (fString, num1) of
                          ("+", 0) => simplifyconstants e2
                        | ("*", 1) => simplifyconstants e2
                        | _ => exp
                  end
              else
                  exp
        | exp => exp

  fun icssimplify exp =
      let val exp = simplifyconstants exp
      in
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
      end
  
  val cvc4exp = cvc4exp o icssimplify

  fun cvc4pred_simple (predString, exp) =
      let val predString = fix predString
      in
          case exp of
              X.Tuple [] => predString << just "()"
            | X.Tuple [first, second] => ("(" << cvc4exp first >> ") " >> predString) @@ (" (" << cvc4exp second >> ")")
            | one => predString << " " << cvc4exp one
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

  fun cvc4pred  sense (pred, exp) =
      cvc4pred_simple (stultify sense (pred, exp))


  fun getEqs cvc4 varMaker =
      [] (* XXX *)

  val r_clock = ref 0
  fun occasional() =
      (r_clock := !r_clock + 1;
       if (!r_clock) mod 2 = 0 then
           (r_clock := 0;
            true)
       else
           false)

   type point = int
   fun push context = (context, ~1)
   fun popto (context, _) = context

(*
   fun popto (cvc4, _) =
      let val cvc4 as CVC4{history, cookie, session} = reaffirm cvc4
          fun back history = case history of
                                 [] => []
                               | Push :: cmds =>
                                     let val _ = eternal_cvc4_transact cvc4 (Other "POP")
                                     in
                                         back cmds
                                     end
                               | _ :: cmds =>
                                     back cmds
          val cvc4 = CVC4{history= [], cookie= Cookie.fresh(), session= session}
          val (cvc4PUSH, empty_result) = recorded_cvc4_transact cvc4 Push
      in
          cvc4PUSH

      end
*)

(* Start a new context *)
   fun popto (_, _) =
      let val cvc4 = Option.valOf (Context.new (getLocation()))
          val _ = print "KABOOM\n"
          val _ = setCurrent cvc4
      in
          cvc4
      end

   fun tickle () =
       if occasional() then
           let val _ = popto (getCurrent(), ~1)
           in
               ()
           end
       else
           ()


  fun rollback (cvc4 as CVC4{history, cookie, ...}) =
         let val _ = replay (getCurrent(), cvc4)
         in
             Cookie.set cookie;
             setCurrent cvc4;
             CHECK "rollback-replay (exit).getCurrent()" (getCurrent());
             cvc4
         end

  fun save cvc4 =
      let 
          val _ = CHECK "save (old) getCurrent()" (getCurrent());
          val _ = setCurrent cvc4
          val _ = CHECK "save (new) getCurrent()" (getCurrent());
      in
          (cvc4,
           fn _ => rollback cvc4
          )
      end

  fun saveForward ics =
      let val (ics, restorer) = save ics
      in
          ics
      end

  and reaffirm (cvc4 as CVC4{cookie, ...}) =
      Cookie.rollback cookie cvc4 (fn () => rollback cvc4)

   fun interpret_result result =
       (* important to check for ".*invalid.*" before ".*valid.*" *)
       if String.isSubstring "invalid" result then  (* False is still false; assertion maintained consistency *)
             false
       else if String.isSubstring "valid" result then  (* Falsehood is entailed: assertion led to inconsistency. *)
             true
       else
           (print ("Cvc4Piped.interpret_result: strange response from cvc4:\n(\n" ^ result ^ "\n)\n");
            raise Option)

 fun assertCoreString cvc4 string =
       let val cvc4 = reaffirm cvc4
              val _ = CHECK "assertCoreString 2" cvc4
              
              val (cvc4PUSHASSERT, result) =
                      half_recorded_cvc4_transact cvc4
                      {recorded1= Assert string,  (*; QUERY(FALSE)"*)
                       eternal2= Other("QUERY(FALSE)")}  (* empty_result *)
              val _ = setCurrent cvc4PUSHASSERT
              val _ = CHECK "assertCoreString 4" cvc4PUSHASSERT
              val _ = dprint (fn () => "assertCore > >    " ^ result ^ "\n < <\n")
          in
             (
              case interpret_result result of  (* False is still false; assertion maintained consistency *)
                  false => Ok (saveForward cvc4PUSHASSERT, [])
               | true =>  (* Falsehood is entailed: assertion led to inconsistency. *)
                    (rollback cvc4;  (* exclude contradictory assertion *)
                     CHECK "assertCoreString 5" (getCurrent());
                     Unsat)
             )
             before
             CHECK "assertCoreString END" (getCurrent())
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

   fun declare (cvc4 as CVC4{history, cookie}, (a, sort)) =
       case sort of
           X.Base sortname =>
               if IcsMapper.mapped a then  (* this check only yields about a 1.02 speedup *)
                   Valid
               else
                   let in if sortname = X.getIntSort() then
                       let val basesortname = "INT"  (* XXX *)
        (*                     val (cvc4, result) = recorded_cvc4_transact ics (IV.toString a ^ " : " ^ basesortname) *)
                           val _ = eternal_cvc4_transact cvc4 (Other (IV.toString a ^ " : " ^ basesortname))
                               (* Need not be recorded, because CVC Lite (like ICS) remembers type declarations across RESETs. *)
                               (* ---CVC3 doesn't remember type declarations across RESETs, but does across POPs. *)
                               (* ---CVC4 doesn't implement RESET, but remembers type declarations across POPs. *)
                       in 
                           Valid
                       end
                          else if sortname = X.getBoolSort() then
        (*                     let val (cvc4, result) = recorded_cvc4_transact ics (IV.toString a ^ " : " ^ "BOOLEAN")
                           in 
                               Ok(cvc4, [])
                           end
        *)
                           let val result = eternal_cvc4_transact cvc4 (Other (IV.toString a ^ " : " ^ "BOOLEAN"))
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
               let fun ggg cvc4 =
                   let val P = X.Constraint.subst [(a0, X.Uvar a)] P
                   in
                       assert (cvc4, P, fn _ => raise Option)
                   end
               in
                   resultize cvc4 (declare (cvc4, (a, sort0))) (fn _ => Unsat) ggg
               end

   and assert (cvc4, W, varMaker) =
        let val _ = dprint (fn () => "Cvc4Piped.assert:  " ^ X.Constraint.toString W ^ "\n")
        in
            case W of
                X.TRUE => Valid
              | X.AND(W1, W2) =>
                    let in case assert (cvc4, W1, varMaker) of
                         Unsat => Unsat
                       | Valid => assert(cvc4, W2, varMaker)
                       | Ok(cvc4, bindings) =>
                             let in case assert(cvc4, W2, varMaker) of
                                  Unsat => Unsat
                                | Valid => Ok(cvc4, bindings)
                                | Ok(cvc4, bindings2) => Ok(saveForward cvc4, bindings @ bindings2)
                             end
                    end
              | X.ALL(a, sort, W0) =>
                    let in case declare (cvc4, (a, sort)) of
                        Unsat => Unsat
                      | Valid => assert(cvc4, W0, varMaker)
                      | Ok(cvc4, bindings) => assert(cvc4, W0, varMaker)
                    end
              | X.EXISTS(a, sort, W0) =>
                    let in case declare (cvc4, (a, sort)) of
                        Unsat => Unsat
                      | Valid => assert(cvc4, W0, varMaker)
                      | Ok(cvc4, bindings) => assert(cvc4, W0, varMaker)
                    end
              | X.EQ(X.Product sorts, X.Tuple es1, X.Tuple es2) =>
                    assert(cvc4, foldl X.AND X.TRUE (map X.EQ (MyList.zip3 (sorts, es1, es2))), varMaker)
              | X.EQ(X.Base basesort, e1, e2) =>
                    if basesort = X.getBoolSort()
                    orelse basesort = X.getIntSort() then 
                        let val s1 = cvc4exp e1
                            val s2 = cvc4exp e2
                            val f = if basesort = X.getBoolSort()
                                    then ") <=> ("
                                    else ") = ("
                        in
                            assertCore cvc4 ("(" << s1 @@ (just f) @@ s2 >> ")")
                        end
                    else
                        raise Option
              | X.PRED(pred, exp) =>
                    let val wholeString = cvc4pred Asserting (pred, exp)
                    in
                        assertCore cvc4 wholeString
                    end
              | X.EQ(sort, e1, e2) => 
                (print ("Ics unknown X.EQ form: " ^ X.Sort.toString sort ^ ", " ^ X.Exp.toString e1 ^ ", " ^ X.Exp.toString e2 ^ "\n"); raise Option)
        (* | X.IMPLIES ... *)
        end

    fun isValidString (cvc4, willow) =
        let 
            val string = willowToString willow
            val cvc4 = reaffirm cvc4
            val _ = CHECK "isValidString 1" cvc4
            val result = eternal_cvc4_transact cvc4 (Other ("QUERY(" ^ string ^ ")"))   (* Not recorded.  ??? *)
            val _ = dprint (fn () => "isValidString >> \n" ^ result ^ "\n <<")
        in
            interpret_result result
            before
            CHECK "isValidString end" (getCurrent())
        end

    val assert = fn arg => (assert arg, [])

    fun isValidEq isValidFn (cvc4, X.Base sortname, (e1, e2)) =
        if e1 = e2 then true
        else
            let
                val s1 = cvc4exp e1
                val s2 = cvc4exp e2
            in
                if sortname = X.getBoolSort() then
                    isValidString (cvc4, (s1 >> " <=> ") @@ s2)
                else
                    isValidString (cvc4, (s1 >> " = ") @@ s2)
            end

    fun isValidPred (cvc4, (pred, e)) =
        let val string = cvc4pred CheckingValidity (pred, e)
            val _ = dprint (fn () => "isValidPred       " ^ willowToString string)
        in
            isValidString(cvc4, string)
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

   fun glork (cvc4 as CVC4{history, ...}) =
       "<<" ^ historyToString history ^ ">>"

   fun reset () =
       (currSession := NONE;
        IcsMapper.reset ();
        Cookie.reset ())

   fun knowsSym cvc4 a = true (* XXX *)

  val rollback =
     fn (_, arg) =>
        (rollback arg)
  
(*  val _ = print "Cvc4Piped RE-EFFECT\n" *)
end
