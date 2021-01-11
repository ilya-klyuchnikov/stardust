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
(* File: Context.sml
 * Author: Joshua Dunfield
 * Contents: Contexts and related data structures used in typechecking.
 *)

signature CONTEXT = sig
  datatype inference_disposition =
      WANT_ORDINARY_TYPE
    | MAINTAIN_PRINCIPALITY

  datatype ordinfo =
       Primvar of {elaboration: string}
     | Uservar

  type rctx
  type mctx
  type ctx = rctx * mctx
  type memo
  type memoinfo
  datatype crumb =
      Typecrumb of Location.location * Sdml.texp
   (* | Typingcrumb of ... *)
  type path = crumb list
  
  type pexp = unit Sdml.Path.pexp
  type pdec = unit Sdml.Path.dec
  type parm = unit Sdml.Path.arm
  type disjuncts = Solve.disjuncts

  val rctxToString : rctx -> string
  val mctxToString : mctx -> string
  val ctxToString : ctx -> string

  val applyMctx : ctx -> (mctx * 'a -> mctx list) -> 'a -> ctx

  val checkSolverState : string -> mctx -> unit

  datatype coninfo =
      Coninfo of {tc : Sdml.tc,
                  basetype : Sdml.texp,
                  contype : Sdml.texp,
                  conjuncts : (Sdml.pv * Sdml.texp) list,
                  unquant_basetype : Sdml.texp,
                  unquant_contype :Sdml.texp,
                  allcons : (Sdml.pv * unit option) list}   (* unit option: NONE if nullary, SOME() if non-nullary *)
  
  datatype typeinfo =
      Typeinfo of
           {indexsort : Indexing.Sorting.t,
            parameters : Sdml.tvinfo list,
            elabTypedecs : Sdml.typedecs}
  
  datatype exinfo =
      UnknownEx
    | SolvedEx of Sdml.texp
    | SectEx of Sdml.texp
    | UnionEx of Sdml.texp

  exception LookupFailure of unit -> string
  
  structure D : sig
    datatype 'pexp declaration =
       Ordinary of Sdml.pv * (Sdml.texp * ordinfo)
     | Linear of Sdml.pv * (Sdml.texp * Sdml.locexp option)
     | Slack of Sdml.pv * (Sdml.locexp * 'pexp)
     | Hint of Sdml.typing
     | UnivType of Sdml.tv * (Sdml.texp option)
     | ExType of Sdml.tv * exinfo
     | MARK of int
    
    type 'pexp Gamma= 'pexp declaration list

    val empty : 'pexp Gamma
    
    val toString : 'pexp declaration -> string
    val GammaToString : 'pexp Gamma -> string
    
    val addOrdinary : Sdml.pv * (Sdml.texp * ordinfo) -> 'pexp Gamma  -> 'pexp Gamma
    val addLinear : Sdml.pv * (Sdml.texp * Sdml.locexp option) -> 'pexp Gamma  -> 'pexp Gamma
    val addSlack : Sdml.pv * (Sdml.locexp * 'pexp) -> 'pexp Gamma  -> 'pexp Gamma
    val addHint : Sdml.typing -> 'pexp Gamma  -> 'pexp Gamma
    val addHints : Sdml.typing list -> 'pexp Gamma  -> 'pexp Gamma
    val addUnivType : Sdml.tv * Sdml.texp option -> 'pexp Gamma  -> 'pexp Gamma
    val addEx : Sdml.tv * exinfo -> 'pexp Gamma  -> 'pexp Gamma

    val setOrd : Sdml.pv -> (Sdml.texp * ordinfo) -> 'pexp Gamma -> 'pexp Gamma
    val setLinear : Sdml.pv -> Sdml.texp * Sdml.locexp option -> 'pexp Gamma -> 'pexp Gamma
    val setSlack : Sdml.pv -> (Sdml.locexp * 'pexp) -> 'pexp Gamma -> 'pexp Gamma
    val setUnivType : Sdml.tv -> Sdml.texp option -> 'pexp Gamma -> 'pexp Gamma
    val setExArtic : Sdml.tv -> (Sdml.tv * exinfo) list -> (exinfo -> exinfo) -> 'pexp Gamma -> 'pexp Gamma

    val lookupOrdinary : Sdml.pv -> 'pexp Gamma -> string -> Sdml.texp * ordinfo
    val lookupLinear : Sdml.pv -> 'pexp Gamma -> string -> (Sdml.texp * Sdml.locexp option)
    val lookupSlack : Sdml.pv -> 'pexp Gamma -> string -> Sdml.locexp * 'pexp
    val lookupUnivType : Sdml.tv -> 'pexp Gamma -> string -> Sdml.texp option

    val getHints : 'pexp Gamma -> Sdml.typing list

    val viable : 'pexp Gamma -> Sdml.tv -> Sdml.texp -> bool

    val prec : 'pexp Gamma -> Sdml.tv -> Sdml.tv -> order
    val order : 'pexp Gamma -> Sdml.tv -> Sdml.tv -> Sdml.tv * Sdml.tv
(*
    val roll : ('a -> 'b option) -> ('a list -> 'c) -> ('a list -> 'b -> 'a list -> ({newPrev:'a list} -> 'c) -> 'c) -> 'a list -> 'c
*)
    val roll : ('pexp declaration -> 'b option)
             -> ('pexp Gamma -> 'c)
             -> ('pexp Gamma -> 'b -> 'pexp Gamma -> ({newPrev:'pexp Gamma} -> 'c) -> 'c)
             -> 'pexp Gamma
             -> 'c
  end

  type G = pexp D.Gamma

  val empty_rctx : (Sdml.tc * Indexing.Sorting.t) list
                         * {exnTC : Sdml.tc, intTC : Sdml.tc, stringTC : Sdml.tc, sumTC : Sdml.tc, inl_pv : Sdml.pv, inr_pv : Sdml.pv}
                         * {elab_Bot : Sdml.pv, exit : Sdml.pv}
                       -> rctx

  val empty_mctx : unit
                       -> mctx

  val empty_ctx : unit -> ctx (* for interactive use *)

  datatype ('a, ''b) ctxt =
      Empty
    | Ctx of (''b) * 'a * ('a, ''b) ctxt
  
  val modifyInfo : ''b -> ('a -> 'a) -> ('a, ''b) ctxt -> ('a, ''b) ctxt

  datatype flexibility = FLEX | NONFLEX
  
  type 'a failure = mctx * (unit -> string) -> 'a

  datatype track = TRK of (*elaboration-ready pattern, with appropriate conjunct*)Sdml.pattern
                          * Sdml.texp  (* relevant type of constructor argument *)
                          * ctx

  val trackToString : track -> string
  val tracksToString : track list -> string

  structure Barrier : sig
    eqtype id
    exception NotInitialized
    val reset : unit -> unit
    val new : unit -> id
    val toString : id -> string
  end 
  
  datatype indexassumption =
      Iall of IndexSym.sym * Indexing.sort
    | Iexists of IndexSym.sym * Indexing.sort
    | Prop of Indexing.constraint
    | Barrier of Barrier.id

  val indexassumptionToString : indexassumption -> string
  val indexToString : indexassumption list -> string
  val domain : indexassumption list -> IndexSym.sym list

  type varmap = Renaming.varmap

  datatype option_track = OTRK of (*elaboration-ready pattern, with appropriate conjunct*)Sdml.pattern option
                          * Sdml.pv   (* conjunct-constructor *)
                          * varmap
                          * (Sdml.texp  (* relevant type of constructor argument (domain) *)
                            * Sdml.texp)  (* constructed type (codomain) *)
                          * ctx
  
  val otrkToString : option_track -> string
  val otrksToString : option_track list -> string
  
  datatype xi_track = XITRK of (*elaboration-ready pattern, with appropriate conjunct*)Sdml.pattern option
                          * Sdml.pv   (* conjunct-constructor *)
                          * Sdml.texp  (* relevant type of constructor argument (domain) *)
                          * ctx

  val getG : mctx -> G
  val getTypes : rctx -> (typeinfo, Sdml.tc) ctxt
  val getCon : rctx -> (coninfo, Sdml.pv) ctxt
  val getDistinguished : rctx -> {exnTC : Sdml.tc, intTC : Sdml.tc, stringTC : Sdml.tc, sumTC : Sdml.tc, inl_pv : Sdml.pv, inr_pv : Sdml.pv}
  val getFunctions : rctx -> {elab_Bot : Sdml.pv, exit : Sdml.pv}

  val elab_Bot : Location.location -> rctx -> Sdml.locexp

  val getIndex : mctx -> indexassumption list
  val getConstraint : mctx -> Indexing.constraint
  val getState : mctx -> (Solve.state * disjuncts) option
  val consistent : mctx -> bool
  val getPath : mctx -> path
  val getVarmap : mctx -> varmap

  val updateIndex : mctx -> (indexassumption list -> indexassumption list) -> mctx
  val updateState : mctx -> ((Solve.state * disjuncts) option -> (Solve.state * disjuncts) option) -> mctx
    val mapUpdateState : mctx -> (Solve.state * disjuncts -> (Solve.state * disjuncts) option) -> mctx
  val updateConstraint : mctx -> (Indexing.constraint -> Indexing.constraint) -> mctx
  val updatePath : mctx -> (path -> path) -> mctx
  val updateVarmap : mctx -> (varmap -> varmap) -> mctx
  
  val updateCon : rctx -> ((coninfo, Sdml.pv) ctxt -> (coninfo, Sdml.pv) ctxt) -> rctx
  val updateTypes : rctx -> ((typeinfo, Sdml.tc) ctxt -> (typeinfo, Sdml.tc) ctxt) -> rctx
  val updateG : mctx -> (G -> G) -> mctx

  val applyEx : mctx * Sdml.texp -> mctx * Sdml.texp
  val getEx : mctx -> Sdml.tv -> exinfo
  val isSectEx    : mctx -> Sdml.tv -> bool
  val isUnionEx : mctx -> Sdml.tv -> bool
  val t2str' : mctx -> Sdml.texp -> string
  val addExtype : mctx -> Sdml.tv -> mctx   (* adds an unknown (unsolved) alpha-hat *)

  val sectEx : mctx -> Sdml.tv -> Sdml.texp -> mctx    (* initial exinfo must be SectEx *)
  val unionEx : mctx -> Sdml.tv -> Sdml.texp -> mctx   (* initial exinfo must be UnionEx *)

  val substExtypevarAuto' : G -> Sdml.texp -> G * Sdml.texp
  val substExtypevarAuto : mctx -> Sdml.texp -> mctx * Sdml.texp

  val substExtypevarNoAuto' : G -> Sdml.texp -> G * Sdml.texp
  val substExtypevarNoAuto : mctx -> Sdml.texp -> Sdml.texp

  val finalSubstLocexp : mctx -> Sdml.locexp -> Sdml.locexp   (* use at end of typechecking only! *)
  
  val rename : varmap -> Sdml.texp -> Sdml.texp
  val renameIndex : varmap -> Indexing.exp -> Indexing.exp
  val renameConstraint : varmap -> Indexing.constraint -> Indexing.constraint
  val renameMctx : varmap -> mctx -> mctx
  
  val pathToString : path -> string
  val recentPaths : path list ref

  val r_forceElim : bool ref

  val conToString : Sdml.pv -> coninfo -> string option

  val forceSingleton : 'a list -> 'a

  (* frame, etc.: Used to mark mctx with a Monnier comma, and then drop the comma and everything after it *)
  val frame : mctx
               -> (mctx -> ('a * mctx * 'd -> 'b) -> 'c)
               -> ('a * mctx * 'd -> 'b)
               -> 'c

  val frameR : mctx
               -> (mctx -> ('a * ctx * 'd -> 'b) -> 'b)
               -> ('a * ctx * 'd -> 'b)
               -> 'b

  val frameRElab : mctx
               -> (mctx -> ('a * ctx * 'c -> 'b) -> 'b)
               -> ('a * ctx * 'c -> 'b)
               -> 'b
  
  val $+ : mctx * crumb -> mctx
  val $- : mctx -> mctx
  
  val %% : mctx * indexassumption -> mctx list
  val ++ : mctx * (Sdml.pv * Sdml.texp) -> mctx

  val +- : mctx * (Sdml.pv * (Sdml.texp * Sdml.locexp option)) -> mctx   (* add linear *)

  val +--+ : mctx * (Sdml.tv * Sdml.texp option) -> mctx  (* add univType *)
  val +--+= : mctx * (Sdml.tv * Sdml.texp option) -> mctx  (* setUnivType *)

  val +~~+ : mctx * (Sdml.pv * (Sdml.locexp * pexp)) -> mctx  (* add slack *)

  val addConinfo : rctx -> Sdml.pv * coninfo -> rctx
  val addTypeinfo : rctx * (Sdml.tc * typeinfo) -> rctx

  val getConjunctOwner : rctx -> (*conjunct*)Sdml.pv -> (*owner constructor*)Sdml.pv
  val getConjunctType : rctx -> (*conjunct*)Sdml.pv -> Sdml.texp
  
  val solveExtype : string -> mctx -> Sdml.tv -> (exinfo -> exinfo) -> mctx
  val solveExtypeArtic : mctx -> Sdml.tv -> Sdml.tv list -> (exinfo -> exinfo) -> mctx
  
  val perm : 'a * 'a -> 'a * 'a

  val unsolvedExtypevars : mctx -> bool
  val solve : mctx -> bool    (* calls Solve.solve *)

  val isSolved : ctx -> bool

  type point
  val isPristine : mctx -> bool
  val push : mctx -> mctx * point
  val popto : mctx * point -> mctx

  datatype infon =
      InfoBarrierID of Barrier.id * Barrier.id
    | InfoIndexSym of IndexSym.sym * IndexSym.sym

  val compose : 'info1 -> ('info1 -> 'info2 option) -> ('info2 -> 'result option) -> 'result option
  val composeList : 'info -> ('info -> 'info option) list -> 'info option

  val eq_record : Indexing.record * Indexing.record -> 'info -> 'info option
  val eq_texp_ignoring_datasorts : Sdml.texp * Sdml.texp -> infon list -> infon list option
  val eq_index : Indexing.exp * Indexing.exp -> infon list -> infon list option

  val &&& : 'a failure -> mctx * Indexing.constraint -> (mctx -> 'a) -> 'a
  val &&  : 'a failure -> mctx * Indexing.constraint -> (mctx -> 'a) -> 'a
  val yellDjs : mctx -> unit
  val %%%% : 'a failure -> mctx * indexassumption -> (mctx -> 'a) -> 'a
  val quantifyUpToBarrier : 'a failure -> (*originalMctx*)mctx -> mctx -> Barrier.id -> (mctx -> 'a) -> 'a

(*  val noUnks' :  domain -> string -> mctx -> Indexing.constraint -> unit = *)
  val noUnks : string -> mctx -> Indexing.constraint -> unit
  val noUnksType : string -> mctx -> Sdml.texp -> unit

  val raise_Dead : 'a failure -> mctx -> (unit -> string) -> 'a
  val raiseDead : 'a failure -> mctx -> Location.location -> (unit -> string) -> 'a

  val setRandomize : (int * int) option -> unit

  datatype memo_control = NoMemo | SemiMemo | FullMemo
  val r_memoize : memo_control ref  
end (* sig CONTEXT *)


structure Context :> CONTEXT = struct

  open Silly
  open Sdml
  
  structure CC = Sdml.ConcreteContext
  structure X = Indexing
  structure DS = Datasorts
  type state = Solve.state
  type disjuncts = Solve.disjuncts

  
  structure IAE = IntStatistEnv
  structure PVAE = PVStatistEnv
  structure TCAE = TCStatistEnv
  structure P = Print
  structure PP = PrettyPrint

  fun PRINT x = print x
  val {dprint, dprnt} =
          Debug.register {full_name= "Context",
                          short_name= "Context"}
  val {dprint= adprint, dprnt= adprnt} =
          Debug.register {full_name= "Context-A",
                          short_name= "Context-A"}

  local
      val index = Option.valOf (Debug.from "Context")
  in
      fun fail s =
          Debug.makeFail index s
  end

  exception LookupFailure of unit -> string
  
  fun pprint s = print (s() ^ "\n")

  val r_forceElim = ref true  (* this MUST be true! *)

  datatype memo_control = NoMemo | SemiMemo | FullMemo
  val r_memoize = ref NoMemo
  


  fun tv2str tv = TV.toString tv
  fun extv2str tv = "'E" ^ Int.toString (TV.toInt tv)
  fun t2str texp = P.pTexp texp
  fun topt2str prefix texpopt =
      case texpopt of
          NONE => ""
        | SOME texp => prefix ^ t2str texp

  fun raise_Dead failure mctx why =
      let in 
          dprint ((fn () => "*** "^why()(*^"   --- " ^ pathToString path ^""*) ^ "\n" ));
(*          recentPaths := (getPath mctx) :: (!recentPaths); *)
          failure (mctx, why)
      end

  fun raiseDead failure mctx loc why = raise_Dead failure mctx (fn () => why() ^ " @ " ^ Location.toString loc)

  structure Barrier = struct
     exception NotInitialized

     type id = int

     val next : id option ref = ref NONE
     
     fun reset() = (next := SOME 10000)
     fun new() =
         case !next of
             NONE => raise NotInitialized
           | SOME n => (n before next := SOME (n + 1))

     fun toString id = "BRR[" ^ Int.toString id ^"]"
  end
  
  datatype indexassumption =
      Iall of IndexSym.sym * X.sort
    | Iexists of IndexSym.sym * X.sort
    | Prop of X.constraint
    | Barrier of Barrier.id
  
  fun lookupIndex sym [] = fail ("lookupIndex: " ^ IndexSym.toString sym ^ " not found")
    | lookupIndex sym ((assn as Iall(sym', sort)) :: rest) = if sym=sym' then assn else lookupIndex sym rest
    | lookupIndex sym ((assn as Iexists(sym', sort)) :: rest) = if sym=sym' then assn else lookupIndex sym rest
    | lookupIndex sym ((Prop _) :: rest) = lookupIndex sym rest
    | lookupIndex sym ((Barrier id) :: rest) = lookupIndex sym rest
  
  fun indexassumptionToString assn =
      case assn of
          Iall(sym, sort) => IndexSym.toString sym ^ " :A: " ^ X.Sort.toString sort
        | Iexists(sym, sort) => IndexSym.toString sym ^ " :E: " ^ X.Sort.toString sort
        | Prop W => X.Constraint.toString W
        | Barrier id => Barrier.toString id

  fun indexToString l = "  " ^ Separate.list ",\n  " (List.rev (List.map indexassumptionToString l))

  fun domain assn =
      let fun f (Iall (a, _)) = SOME a
            | f (Iexists (a, _)) = SOME a
            | f (Prop _) = NONE
            | f (Barrier _) = NONE
      in
            List.mapPartial f assn
      end
      
  datatype ('a, ''b) ctxt =
      Empty
    | Ctx of (''b) * 'a * ('a, ''b) ctxt
  
  fun ctxtlength Empty = 0
    | ctxtlength (Ctx(_, _, ctxt)) = 1 + ctxtlength ctxt

(*
  fun @@@ (Empty, ctxt2) = ctxt2
    | @@@ (Ctx(x, a, ctxt1), ctxt2) = Ctx(x, a, @@@(ctxt1, ctxt2))
  infix 5 @@@
*)

  datatype crumb =
      Typecrumb of Location.location * texp
   (* | Typingcrumb of ... *)
  withtype path = crumb list
  
  fun crumbToString c =
      let in case c of
          Typecrumb (loc, texp) => "(" ^ t2str texp ^ " @ " ^ Location.toString loc ^ ")"
      end
  fun pathToString path = Separate.list ", " (map crumbToString path)

  val recentPaths : path list ref = ref []

  datatype ordinfo =
       Primvar of {elaboration: string}
     | Uservar

  datatype coninfo =
      Coninfo of {tc : Sdml.tc,
                  basetype : texp,
                  contype : texp,
                  conjuncts : (Sdml.pv * Sdml.texp) list,
                  unquant_basetype : texp,
                  unquant_contype : texp,
                  allcons : (Sdml.pv * unit option) list}   (* unit option: NONE if nullary, SOME() if non-nullary *)
  
  datatype typeinfo =
      Typeinfo of
           {indexsort : X.Sorting.t,
            parameters : Sdml.tvinfo list,
            elabTypedecs : Sdml.typedecs}
  
  datatype exinfo =
      UnknownEx
    | SolvedEx of Sdml.texp
    | SectEx of Sdml.texp
    | UnionEx of Sdml.texp
  
  type varmap = Renaming.varmap

  fun productize f (x, y) = (f x, f y)

  datatype flexibility = FLEX | NONFLEX

  structure Declaration = struct
    datatype 'pexp declaration =
       Ordinary of pv * (texp * ordinfo)
     | Linear of pv * (texp * locexp option)
     | Slack of pv * (locexp * 'pexp)
     | Hint of typing
     | UnivType of tv * (texp option)
     | ExType of tv * exinfo
     | MARK of int

    val markCount : int ref = ref 3000

    type 'pexp Gamma = 'pexp declaration list

    val empty = []

    fun eq (d1, d2) = false (*XXX*)

    fun eqG (G1, G2) = (List.all eq (ListPair.zip (G1, G2))) handle ListPair.UnequalLengths => false
    
    fun toString d = case d of
      Ordinary (pv, (A, Uservar)) => PV.toShortString pv ^ " : " ^ P.pTexp A
    | Ordinary (pv, (A, Primvar {elaboration= elaboration})) =>
           PV.toShortString pv ^ " :prim: " ^ P.pTexp A ^ " = \"" ^ elaboration ^ "\""
    | Linear (pv, (A, locexpOptionXXX)) => PV.toString pv ^ ":LIN:" ^ P.pTexp A
    | Slack (pv, (locexp, _)) => "~" ^ PV.toString pv
    | Hint typing => P.pTyping typing
    | UnivType (tv, topt) => TV.toString tv ^ topt2str "==" topt
    | ExType (tv, exinfo) =>
        let val sym = TV.toString tv
        in
           case exinfo of
             UnknownEx     => "[E? " ^ sym ^ "?]"
           | SolvedEx texp => "[E " ^ sym ^ ":= " ^ P.pTexp texp ^ "]"
           | SectEx texp   => "[E " ^ sym ^ ":/\\= " ^ P.pTexp texp ^ "]"
           | UnionEx texp  => "[E " ^ sym ^ ":\\/= " ^ P.pTexp texp ^ "]"
        end
    | MARK m => "||" ^ Int.toString m ^ "||"
    
    fun declIsWorthy (Ordinary (_, (_, Primvar _))) = false
      | declIsWorthy _  = true

    fun GammaToString G = Separate.list ",  " (map toString (List.rev (List.filter declIsWorthy G))) ^ "\n"

    (* Assumes var does not appear more than once *)
    fun setOrd var info G = let val self = setOrd var info in case G of
          [] => []
        | (d as Ordinary (var', info')) :: rest =>
              (if var = var' then Ordinary(var', info) else d) :: self rest
        | d :: rest => d :: self rest
      end

    fun setLinear var info G = let val self = setLinear var info in case G of
          [] => []
        | (d as Linear (var', info')) :: rest =>
              (if var = var' then Linear(var', info) else d) :: self rest
        | d :: rest => d :: self rest
      end

    fun setSlack var info G = let val self = setSlack var info in case G of
          [] => []
        | (d as Slack (var', info')) :: rest =>
              (if var = var' then Slack(var', info) else d) :: self rest
        | d :: rest => d :: self rest
      end

    fun setUnivType var info G = let val self = setUnivType var info in case G of
          [] => (print "setUnivType: not found?!\n"; [])
        | (d as UnivType (var', info')) :: rest =>
               if var = var'
               then UnivType(var', info) :: rest
               else d :: self rest
        | d :: rest => d :: self rest
      end

    fun modEx var fFound fNotFound G = let val self = modEx var fFound fNotFound in case G of
          [] => fNotFound()
        | (d as ExType (var', info')) :: rest =>
              if var = var' then
                (*XXX: should check that var does not appear in rest*)
                let val (ds, other) = fFound(var', info')
                in
                  (ds @ rest, other)
                end
              else
                let val (ds, other) = self rest
                in
                  (d :: ds, other)
                end

        | d :: rest =>
            let val (ds, other) = self rest
            in
              (d :: ds, other)
            end
     end

(* 
    fun setExArtic var articulation info G = let val self = setExArtic var articulation info in case G of
          [] => []
        | (d as ExType (var', info')) :: rest =>  (* XXX should check info' = UnknownEx *)
              (if var = var' then
                 [ExType(var', info)] @ (List.map ExType articulation)
               else [d]) @ self rest
        | d :: rest => d :: self rest
      end
*)
    fun setExArtic var articulation infoFn G =
      #1 (modEx var
            (*fFound=*)  (fn (var', info') => if var <> var' then raise Option
                                              else
                                                  ([ExType(var', infoFn info')] @ (List.map ExType articulation), ()))
            (*fNotFound=*) (fn () => raise Option(*XXX*))
            G)
    
    fun setEx var info G = setExArtic var [] info G

    fun exToAssoc G = case G of
       [] => []
     | ExType(tv, SolvedEx texp)  :: rest => (tv, texp) :: (exToAssoc rest)
     | ExType(tv, SectEx texp)    :: rest => (tv, texp) :: (exToAssoc rest)
     | ExType(tv, UnionEx texp)   :: rest => (tv, texp) :: (exToAssoc rest)
     | ExType(tv, UnknownEx)      :: rest => exToAssoc rest
     | d :: rest => exToAssoc rest

    fun assocToString assoc =
       Separate.list ",\n" (List.map (fn (tv, texp) => tv2str tv ^ " |--> " ^ P.pTexp texp) assoc)

    fun unsolvedExtypevarsAux G = case G of
       [] => []
     | ExType(tv, SolvedEx texp)  :: rest => unsolvedExtypevarsAux rest
     | ExType(tv, SectEx texp)    :: rest => unsolvedExtypevarsAux rest
     | ExType(tv, UnionEx texp)   :: rest => unsolvedExtypevarsAux rest
     | ExType(tv, UnknownEx)      :: rest => tv :: unsolvedExtypevarsAux rest
     | d :: rest => unsolvedExtypevarsAux rest

    fun add d G = ((*print ("add " ^ toString d ^ "\n"); *) d :: G)
    fun addOrdinary d G = add (Ordinary d) G
    fun addLinear d G = add (Linear d) G
    fun addSlack d G = add (Slack d) G
    fun addHint d G = add (Hint d) G
    fun addHints ds G = case ds of [] => G | d::ds => addHints ds (addHint d G)
    fun addUnivType d G = add (UnivType d) G
    fun addEx d G = add (ExType d) G

    fun rlookupX test printer G info = case G of 
        [] => ( (*PRINT ("rlookupX: " ^ printer() ^ " (" ^ info ^ ")\n");*)
                      raise LookupFailure (fn () => "rlookupX " ^ printer() ^ " (" ^ info ^ ") " (* ^ rctxToString fullctx *)))
      | d :: rest =>
            let in
                case test d of
                    NONE => rlookupX test printer rest info
                  | SOME record => record
            end
    fun rlookup test printer G info = 
        rlookupX test printer G info

    fun lookupOrdinary pv = rlookup (fn x => (case x of Ordinary(x, record)  => if x = pv then SOME record else NONE | _ => NONE))
                                    (fn () => PV.toString pv)
    fun lookupLinear pv     = rlookup (fn x =>
                                                        let in 
                                                            case x of Linear(x, record)      =>
                                                                      (if x = pv then SOME record else
                                                                       NONE)
                                                                    | _ => NONE
                                                        end)
                                    (fn () => PV.toString pv)
    fun lookupSlack pv      = rlookup (fn x => (case x of Slack(x, record)        => if x = pv then SOME record else NONE | _ => NONE))
                                    (fn () => PV.toString pv)
    fun lookupUnivType tv = rlookup (fn x => (case x of UnivType(x, record) => if x = tv then SOME record else NONE | _ => NONE))
                                    (fn () => TV.toString tv)
  
    fun getHints G = List.mapPartial (fn d => (case d of Hint h => SOME h | _ => NONE)) G

    fun roll filter ending f G =
      let fun aux prev next = case next of
        [] => ending prev
      | first :: rest =>
          let in case filter first of
             NONE => aux (first :: prev @ [first]) rest
           | SOME contents => f prev contents rest (fn {newPrev} => aux newPrev rest)
          end
      in
        aux empty G
      end

    fun typevarDeclared G tv =
      List.exists (fn UnivType(tv', _) => tv' = tv | _ => false) G

    fun extypevarDeclared G tv =
      List.exists (fn ExType(tv', _) => tv' = tv | _ => false) G

    fun pvDeclared G pv =
      List.exists
        (fn Ordinary(pv', _) => pv' = pv
          | Linear(pv', _) => pv' = pv
          | Slack(pv', _) => pv' = pv
          | _ => false) G

    fun inScope G A = case A of 
        Typevar tv => typevarDeclared G tv
      | Extypevar tv => extypevarDeclared G tv
      | All(tv, universe, A0) => inScope (UnivType(tv, NONE) :: G) A0
      | Arrow(A1, A2) => inScope G A1 andalso inScope G A2
      | Sect(A1, A2) => inScope G A1 andalso inScope G A2
      | Union(A1, A2) => inScope G A1 andalso inScope G A2
      | Rsect(A1, A2) => inScope G A1 andalso inScope G A2
      | Runion(A1, A2) => inScope G A1 andalso inScope G A2
      | Product As => List.all (inScope G) As
      | Tycon(tc, _, As)  => List.all (inScope G) As
      | Univ(a, sort, A0) => inScope G A0
      | Exis(a, sort, A0) => inScope G A0
      | Top => true
      | Bot => true
      | Record(fld, A0) => inScope G A0
      | Implies(P, A0) => inScope G A0
      | Conj(P, A0) => inScope G A0

    fun prec G ex1 ex2 = case G of
       [] => fail "prec"
     | ExType(tv, _) :: rest =>
          if tv=ex1 then (* ex1 is first in the list, therefore second logically, so ex1 ">" ex2 *)
            (if extypevarDeclared rest ex2 then GREATER
             else fail "prec ??")
          else if tv=ex2 then (* ex2 is first in the list, therefore second logically, so ex1 "<" ex2 *)
            (if extypevarDeclared rest ex1 then LESS
             else fail "prec ??")
          else prec rest ex1 ex2
     | d :: rest => prec rest ex1 ex2


    fun viable G exalpha A = case G of
       [] => fail "viable"
     | ExType(tv, _) :: rest =>
          if tv=exalpha then  (* `rest' is context under which A must be well-formed *)
            inScope rest A
          else viable rest exalpha A
     | d :: rest => viable rest exalpha A

    fun order G ex1 ex2 =
      case prec G ex1 ex2 of
        LESS => (ex1, ex2)
      | GREATER => (ex2, ex1)

    fun verifyG G =
      let fun pvNotDup context pv =
              if pvDeclared context pv then (PRINT ("duplicate " ^ PV.toString pv ^ "\n"); false) else true
          fun tvNotDup context tv =
              if typevarDeclared context tv then (PRINT ("duplicate " ^ TV.toString tv ^ "\n"); false) else true
          fun scope context A =
              if inScope context A then true
              else (PRINT ("type " ^ t2str A ^ " not in scope in\n" ^ GammaToString context); false)

          fun aux context [] = true
            | aux context (this::rest) =
                let in case this of
                  Ordinary (pv, (A, _)) => pvNotDup context pv andalso scope context A
                | Linear (pv, (A, elabOptXXX)) => pvNotDup context pv andalso scope context A
                | Slack (pv, (locexp, _)) => pvNotDup context pv
                | Hint typing => true
                | UnivType (tv, topt) =>
                     tvNotDup context tv
                     andalso
                       let in
                         case topt of NONE => true | SOME solutionType => scope context solutionType
                       end
                | MARK m => true
                | ExType (tv, exinfo) =>
                     tvNotDup context tv
                     andalso
                       let in
                         case exinfo of UnknownEx => true
                                      | SolvedEx solutionType => scope context solutionType
                                      | SectEx solutionType => scope context solutionType
                                      | UnionEx solutionType => scope context solutionType
                       end
                end
                andalso aux (this :: context) rest
      in
        aux [] (List.rev G)
      end

      fun mark (G : 'a Gamma) : (('a Gamma -> 'a Gamma) * 'a Gamma) =
       let val m = !markCount
           val _ = markCount := !markCount + 1
       in
         (cut m, (MARK m) :: G)
       end

      and cut m G = let fun cut revdSuffix G = case G of
          [] => fail "cut: trying to cut rock"
        | x :: rest => let in case x of
             MARK m' =>
               if m = m' then
                 let
                   val suffix = List.rev revdSuffix
(*                   val _ = PRINT ("CUT " ^ GammaToString rest ^ " --8<--- " ^ GammaToString suffix ^ " --->8--" ^ "\n")
*)
                 in
                   rest
                 end
               else cut (x :: revdSuffix) rest
           | _ => cut (x :: revdSuffix) rest
          end
     in
       cut empty G
     end
  end

  structure D = Declaration

  datatype inference_disposition =
      WANT_ORDINARY_TYPE
    | MAINTAIN_PRINCIPALITY

  datatype rctx = RCTX of   (* regular context *)
        { 
(* (formerly) Program-invariant parts of context *)
         con : (coninfo, pv) ctxt              (* Constructors:  (basetype, contype) *)
       , types : (typeinfo, tc) ctxt           (* Type information *)
       , distinguished : {exnTC : tc, intTC : tc, stringTC : tc, sumTC : tc, inl_pv : pv, inr_pv : pv}
       , functions : {elab_Bot : pv, exit : pv}
       }
  and mctx = MCTX of  (* "monadic" context *)
      {G : G
       , index : indexassumption list          (* Index environment *)
       , constraint : X.constraint
       , state : (state * disjuncts) option    (* Solver state (NONE means inconsistent) *)
       , path : path                           (* `Breadcrumbs' for error reporting *)
       , varmap : varmap
      }
  and memoinfo =
      MInfer of (inference_disposition * ctx) * ((mctx * Sdml.texp) option)
    | MCheck of (ctx * texp) * (ctx list)
    | MSubtype of (ctx * texp * texp) * (mctx option)  
  withtype (* memo = memoinfo list ref *)
      memo = unit
  and pexp = unit (*(memoinfo list ref)*) Sdml.Path.pexp   (* MLton, how do I hate thee? *)
  and ctx = rctx * mctx
  and G = (unit Sdml.Path.pexp) D.Gamma   (* MLton, how do I hate thee? *)
  
  type pdec = memo Sdml.Path.dec
  type parm = memo Sdml.Path.arm

  type 'a failure = mctx * (unit -> string) -> 'a

  datatype track = TRK of (*elaboration-ready pattern, with appropriate conjunct*)Sdml.pattern
                          * Sdml.texp  (* relevant type of constructor argument *)
                          * ctx

  datatype option_track = OTRK of (*elaboration-ready pattern, with appropriate conjunct*)Sdml.pattern option
                          * Sdml.pv   (* conjunct-constructor *)
                          * varmap
                          * (Sdml.texp  (* relevant type of constructor argument (domain) *)
                            * Sdml.texp)  (* constructed type (codomain) *)
                          * ctx

  datatype xi_track = XITRK of (*elaboration-ready pattern, with appropriate conjunct*)Sdml.pattern option
                          * Sdml.pv   (* conjunct-constructor *)
                          * Sdml.texp  (* relevant type of constructor argument (domain) *)
                          * ctx
    
(*  val universalHistoryOfInfamy : memo = ref [] *)
  
  val r_rnd : Random.rand option ref = ref NONE (*(Random.rand (12851, 149403))*)
  
  fun setRandomize seed =
      case seed of
          NONE => (r_rnd  := NONE)
        | SOME seed => (r_rnd := SOME (Random.rand seed))

  fun rand rnd =
      case Random.randRange (0,1) rnd of
          0 => false
        | _ => true

  fun perm (a, b) =
      let val rnd = !r_rnd
      in
          case rnd of
              NONE => (a, b)
            | SOME rnd =>
                if rand rnd then (b, a) else (a, b)
      end

  datatype infon =
      InfoBarrierID of Barrier.id * Barrier.id
    | InfoIndexSym of IndexSym.sym * IndexSym.sym
  
  fun eq_ctxt eqf info (Empty, Empty) = SOME info
    | eq_ctxt eqf info (Ctx(pv1, stuff1, ctxt1), Ctx(pv2, stuff2, ctxt2)) =
          if pv1 <> pv2 then NONE
          else
              let in case eqf (stuff1, stuff2) info of
                  NONE => NONE
                | SOME info => eq_ctxt eqf info (ctxt1, ctxt2)
              end
    | eq_ctxt eqf _ (_, _) = NONE

  fun compose info part1 part2 =
      case part1 info of
          NONE => NONE
        | SOME info => part2 info

  fun composeList info parts =
      case parts of
          [] => SOME info
        | (part1 :: parts) => compose info part1 (fn info => composeList info parts)

  fun eq_opt eqf (part1, part2) info =
      case (part1, part2) of
          (NONE, NONE) => SOME info
        | (SOME part1, SOME part2) => eqf (part1, part2) info
        | (_, _) => NONE

  fun eq_index (index1, index2) info =
      case (index1, index2) of
          (X.Uvar sym1, X.Uvar sym2) =>
              let val assoc = List.mapPartial (fn InfoIndexSym stuff  => SOME stuff | _ => NONE) info
                  val sym1' = case Assoc.getOpt assoc sym1 of
                                  NONE => sym1
                                | SOME sym1' => (print ("using infon: " ^ IndexSym.toString  sym1 ^ " |-> " ^ IndexSym.toString sym2 ^ "\n");
                                                 sym1')
              in
                  if sym1' = sym2 then SOME info
                  else SOME (InfoIndexSym(sym1', sym2) :: info)
              end
        | (X.Evar sym1, X.Evar sym2) => eq_index (X.Uvar sym1, X.Uvar sym2) info
    | (X.Nil sym1, X.Nil sym2) => if sym1 <> sym2 then NONE else SOME info
    | (X.Literal(sort1, string1), X.Literal(sort2, string2)) =>
          if sort1 <> sort2 orelse string1 <> string2 then NONE else SOME info
    | (X.App(sym1, exp1), X.App(sym2, exp2)) =>
          if sym1 <> sym2 then NONE
          else eq_index (exp1, exp2) info
    | (X.Tuple [], X.Tuple []) => SOME info
    | (X.Tuple (exp1 :: exps1), X.Tuple (exp2 :: exps2)) =>
          compose info (eq_index (exp1, exp2)) (eq_index (X.Tuple exps1, X.Tuple exps2))
    | (X.Proj(n1, exp1), X.Proj(n2, exp2)) =>
          if n1 <> n2 then NONE
          else eq_index (exp1, exp2) info
    | (X.True, X.True) => SOME info
    | (X.False, X.False) => SOME info
    | (X.NODIM, X.NODIM) => SOME info
    | (ix1, ix2) => NONE
(*      (print "NONEXH"; print (X.Exp.toString ix1 ^ "  =?=  " ^ X.Exp.toString ix2 ^ "\n"); raise Option) *)

  val eq_index = eq_index
      : X.exp * X.exp -> infon list -> infon list option

  fun eq_constraint (W1, W2) info =
      case (W1, W2) of
          (X.EQ (_, left1, right1), X.EQ (_, left2, right2)) =>
              compose info (eq_index (left1, left2)) (eq_index (right1, right2))
        | (X.PRED(sym1, exp1), X.PRED(sym2, exp2)) =>
              if sym1 <> sym2 then NONE
              else eq_index (exp1, exp2) info
        | (X.TRUE, X.TRUE) => SOME info
        | (X.AND (left1, right1), X.AND (left2, right2)) =>
              compose info (eq_constraint (left1, left2)) (eq_constraint (right1, right2))
        | (X.OR (left1, right1), X.OR (left2, right2)) =>
              compose info (eq_constraint (left1, left2)) (eq_constraint (right1, right2))
        | (X.IMPLIES (left1, right1), X.IMPLIES (left2, right2)) =>
              compose info (eq_constraint (left1, left2)) (eq_constraint (right1, right2))
        | (X.ALL(sym1, sort1, W1), X.ALL(sym2, sort2, W2)) =>
              if sort1 <> sort2 then NONE   (* XXX *)
              else eq_constraint (W1, W2) (InfoIndexSym(sym1, sym2) :: info)
        | (X.EXISTS(sym1, sort1, W1), X.EXISTS(sym2, sort2, W2)) =>
              if sort1 <> sort2 then NONE   (* XXX *)
              else eq_constraint (W1, W2) (InfoIndexSym(sym1, sym2) :: info)
        | (_, _) => NONE

  fun eq_record (r1, r2) info =
      if X.eq_record (r1, r2) then SOME info else NONE

  fun eq_texp_ABSTRACT f (texp1, texp2) info =
    let val texp1 = Inject.clean texp1
        val texp2 = Inject.clean texp2
        val eq_texp = eq_texp_ABSTRACT f
    in
      case (texp1, texp2) of
     (Arrow(left1, right1), Arrow(left2, right2)) =>
         compose info (eq_texp (left1, left2)) (eq_texp (right1, right2))
    | (Product [], Product []) =>
          SOME info
    | (Product (texp1::texps1), Product (texp2::texps2)) =>
          compose info (eq_texp (texp1, texp2)) (eq_texp (Product texps1, Product texps2))
    | (Tycon(tc1, index1, []), Tycon(tc2, index2, [])) =>  (*PPP*)
          if not (f (tc1, tc2)) then NONE
          else eq_record (index1, index2) info
    | (Sect(A1, B1), Sect(A2, B2)) =>
          compose info (eq_texp (A1, A2)) (eq_texp (B1, B2))
    | (Union(A1, B1), Union(A2, B2)) =>
          compose info (eq_texp (A1, A2)) (eq_texp (B1, B2))
    | (Rsect(A1, B1), Rsect(A2, B2)) =>
          compose info (eq_texp (A1, A2)) (eq_texp (B1, B2))
    | (Runion(A1, B1), Runion(A2, B2)) =>
          compose info (eq_texp (A1, A2)) (eq_texp (B1, B2))
    | (Univ(a1, sort1, A1), Univ(a2, sort2, A2)) =>
          if sort1 <> sort2 then NONE  (* XXX *)
          else eq_texp (A1, A2) (InfoIndexSym(a1, a2) :: info)
    | (Exis(a1, sort1, A1), Exis(a2, sort2, A2)) =>
          if sort1 <> sort2 then NONE  (* XXX *)
          else eq_texp (A1, A2) (InfoIndexSym(a1, a2) :: info)
    | (Top, Top) => SOME info
    | (Bot, Bot) => SOME info
    | (Record(fld1, A1), Record(fld2, A2)) =>
          if fld1 <> fld2 then NONE 
          else eq_texp (A1, A2) info
    | (Implies(W1, A1), Implies(W2, A2)) =>
          compose info (eq_constraint (W1, W2)) (eq_texp (A1, A2))
    | (Conj(W1, A1), Conj(W2, A2)) =>
          compose info (eq_constraint (W1, W2)) (eq_texp (A1, A2))
    | (_, _) => NONE
   end

  fun eq_texp (texp1, texp2) info =
      eq_texp_ABSTRACT (op=) (texp1, texp2) info

  fun eq_texp_ignoring_datasorts (texp1, texp2) info =
      eq_texp_ABSTRACT (fn (tc1, tc2) => DS.blitheRefines tc1 = DS.blitheRefines tc2) (texp1, texp2) info

  fun eqf_true (_, _) info =
      SOME info

  fun eq_rctx (RCTX{con= con1, types= types1, distinguished= _, functions= _},
               RCTX{con= con2, types= types2, distinguished= _, functions= _})
      info
      =
  case
      composeList info
      [(* fn info => eq_ctxt eqf_true info (slack1, slack2),    Ignore slack-vars: they will always have the same expansions at a given program point. *)
       (* fn info => eq_ctxt eqf_true info (down1, down2),    Ignore downward-vars: they will always have the same expansions at a given program point. *)
       (* Ignore constructor typing, since it never varies. *)
       (* Ignore hints, because we're lazy. XXX *)
       ]
  of 
      NONE => (dprnt "eq_rctx _FAIL_\n"; NONE)
    | SOME x => (dprnt "eq_rctx _SUCC_\n"; SOME x)

  
  fun eq_list eqf (list1, list2) info =
      case (list1, list2) of
          ([], []) => SOME info
        | (x1::xs1, x2::xs2) => compose info (eqf (x1, x2)) (eq_list eqf (xs1, xs2))
        | (_, _) => NONE

  fun eq_indexassumption (assn1, assn2) info =
      case (assn1, assn2) of
          (Iall(sym1, sort1), Iall(sym2, sort2)) =>
              SOME info  (* XXX *)
        | (Iexists(sym1, sort1), Iexists(sym2, sort2)) =>
              SOME info  (* XXX *)
        | (Prop W1, Prop W2) =>
              eq_constraint (W1, W2) info
        | (Barrier id1, Barrier id2) =>
              let val _  = dprint (fn () => "eq_indexassumption InfoBarrierID(" ^ Barrier.toString id1 ^ ", " ^ Barrier.toString id2 ^" )\n") in
              SOME (InfoBarrierID(id1, id2) :: info)
              end
        | (_, _) => NONE

  type symsym = IndexSym.sym * IndexSym.sym
  val eq_indexassumption = eq_indexassumption
      : (indexassumption * indexassumption -> infon list -> infon list option)

  fun solve (mctx as MCTX{state, ...}) = 
      case state of
          NONE => false
        | SOME (state, djs) => Solve.solve state
  
  fun stripRCTX (RCTX stuff) = stuff
  fun stripMCTX (MCTX stuff) = stuff
  
  fun checkG G =
      (  if not (D.verifyG G) then
           (PRINT ("************* GAMMA BAD *************\n"
                ^ D.GammaToString G
                ^ "****************************************\n")
          ; fail "GAMMA BAD" )
         else ()
       ; G  )

       
  fun checkSolverState info (MCTX {index, state, ...}) =
    let fun checkIndexAssn assn = case assn of
                Iall(a, _) => let in case state of 
                                             NONE => (* print ("checkSolverState(" ^ info ^ "): solver state inconsistent, thus doesn't have " ^ IndexSym.toString a ^"\n") *) ()
                                           | SOME (state, _) =>
                                                if Solve.knowsSym state a then
                                                    ()
                                                else
                                                    print ("checkSolverState(" ^ info ^ "): solver doesn't know " ^ IndexSym.toString a ^ "\n")
                              end
              | Iexists(a, _) => () (* XXX? *)
              | Prop W => ()   (* XXX should check variables in constraint *)
              | Barrier id => ()
    in
      List.app checkIndexAssn index
    end

  val getG = checkG o #G o stripMCTX
  val getTypes = #types o stripRCTX
  val getCon = #con o stripRCTX
  val getDistinguished = #distinguished o stripRCTX

  val getFunctions = #functions o stripRCTX

  fun elab_Bot loc rctx =
      let val {elab_Bot, ...} = getFunctions rctx
      in
          (loc,
           Sdml.App ((loc, Sdml.Var elab_Bot), (loc, Sdml.Tuple [])))
      end
  

  val getIndex = #index o stripMCTX
  val getConstraint = #constraint o stripMCTX
  val getState = #state o stripMCTX
  val getPath = #path o stripMCTX
  val getVarmap = #varmap o stripMCTX
  
  fun consistent mctx =
      Option.isSome (getState mctx)
  
  fun updateTypes (RCTX {con= con, types= types, distinguished= distinguished, functions= functions}) f =
      RCTX{con= con, types= f types, distinguished= distinguished, functions= functions}
  fun updateG (MCTX {G=G, index= index,  path= path, state= state, constraint= constraint, varmap= varmap}) f =
    let (* val _ = PRINT ("###?" ^ D.GammaToString G)
        val G = D.roll SOME (fn prev => prev) (fn prev => fn contents => fn rest => fn kRoll => kRoll {newPrev= prev @ [contents]}) G
        val _ = PRINT ("###$" ^ D.GammaToString G) *)
        val len = List.length G
        val G = checkG G
        val newG = f G
(*        val newLen = List.length newG
        val _ = if newLen < len then PRINT ("************* WARNING: GAMMA: "
                                          ^ D.GammaToString G ^ "\n------------->\n" ^ D.GammaToString newG ^ "\n")
                else ()
*)
        val newG = checkG newG
    in
      MCTX{G= newG,  index= index,  path= path, state= state, constraint= constraint, varmap= varmap}
    end
  fun updateCon (RCTX {con= con, types= types, distinguished= distinguished, functions= functions}) f =
      RCTX{con= f con, types= types, distinguished= distinguished, functions= functions}

  fun Solve_ok_state_djs (state, djs) =
      (Solve.ok_state state, djs)

  fun updateIndex (MCTX {G= G, index,  path= path, state= state, constraint= constraint, varmap= varmap}) f =
      let val mctx' = MCTX{G= G, index= f index,  path= path, state= state, constraint= constraint, varmap= varmap}
          val _ = checkSolverState "updateIndex" mctx'
      in
        mctx'
      end
  fun updateState (MCTX {G= G, index= index,  path= path, state= state, constraint= constraint, varmap= varmap}) f =
      let val mctx' = MCTX{G= G, index= index,  path= path, state= Option.map Solve_ok_state_djs (f state), constraint= constraint, varmap= varmap}
          val _ = checkSolverState "updateState" mctx'
      in
        mctx'
      end

  fun mapUpdateState ctx f =
      updateState ctx (Option.mapPartial f)
  fun updateConstraint (MCTX {G= G, index= index,  path= path, state= state, constraint= constraint, varmap= varmap}) f =
      MCTX{G= G, index= index,  path= path, state= state, constraint= f constraint, varmap= varmap}
  fun updatePath (MCTX {G= G, index= index,  path= path, state= state, constraint= constraint, varmap= varmap}) f =
      MCTX{G= G, index= index,  path= f path, state= state, constraint= constraint, varmap= varmap}
  fun updateVarmap (MCTX {G= G, index= index,  path= path, state= state, constraint= constraint, varmap= varmap}) f =
      MCTX{G= G, index= index,  path= path, state= state, constraint= constraint, varmap= f varmap}

  fun splayMapUpdateState ctx g =
      let val states = g (getState ctx)
      in
          case states of
              [] => [updateState ctx (fn _ => NONE)]
            | states =>
                  map (fn state => updateState ctx (fn _ => SOME state)) states
      end

  fun ctxtToString f Empty = "."
    | ctxtToString f (Ctx(pv, assn, ctxt)) =
          let in
              case f pv assn of
                  NONE => ctxtToString f ctxt
                | SOME s => (ctxtToString f ctxt) ^ ", " ^ s
          end

  fun allconentryToString (pv, unitopt) = "(" ^ PV.toString pv ^ ", "
                                          ^ (case unitopt of NONE => "NONE" | SOME() => "SOME()")
                                          ^ ")"

  fun conToString pv (Coninfo{contype, basetype, allcons, ...})
    =
    SOME (PV.toString pv ^ " : " ^ P.pTexp contype
          ^ " (basetype " ^ P.pTexp basetype ^"; "
          ^ "  allcons = " ^ Separate.list ", " (List.map allconentryToString allcons)
          ^ ")")

  fun sectEx mctx var B2 =
    updateG mctx (fn G =>
    #1 (D.modEx var
           (*fFound=*) (fn (var', SectEx B1) =>
                                                ([D.ExType(var', SectEx (Sect(B1, B2)))], ())
                                    | (var', UnknownEx) =>
                                                ([D.ExType(var', SectEx B2)], ()))
           (*fNotFound=*) (fn () => raise Option)
           G))

  fun unionEx mctx var B2 =
    updateG mctx (fn G =>
    #1 (D.modEx var
           (*fFound=*) (fn (var', UnionEx B1) =>
                                                ([D.ExType(var', UnionEx (Union(B1, B2)))], ())
                                    | (var', UnknownEx) =>
                                                ([D.ExType(var', UnionEx B2)], ()))
           (*fNotFound=*) (fn () => raise Option)
           G))


(* use:
      frame mctx (fn mctx => ___check failure (rctx, mctx ++ (x, A)) (_, _) B___) k
   Note that k is OUTSIDE the fn
*)
      fun frame mctx f k =
          let val (scissors, G) = D.mark (getG mctx)
              val mctx = updateG mctx (fn _ => G)
              val kCut = fn (failure, mctx, result) =>
                           let val mctx = updateG mctx scissors in
                             k (failure, mctx, result)
                           end
          in
            (f mctx) kCut
          end

      and frameR mctx f k =
          let val (scissors, G) = D.mark (getG mctx)
              val mctx = updateG mctx (fn _ => G)
              val kCut = fn (failure, (rctx, mctx), elab) =>
                           let val mctx = updateG mctx scissors in
                             k (failure, (rctx, mctx), elab)
                           end
          in
            (f mctx) kCut
          end

      and frameRElab mctx f k =
          let val (scissors, G) = D.mark (getG mctx)
              val mctx = updateG mctx (fn _ => G)
              val kCut = fn (failure, (rctx, mctx), elab) =>
                           let val mctx = updateG mctx scissors in
                             k (failure, (rctx, mctx), elab)
                           end
          in
            (f mctx) kCut
          end


  fun addExtype mctx tv =
      updateG mctx (D.addEx (tv, UnknownEx))




  fun substExtypevarNoAuto' G texp =
     let val self = substExtypevarNoAuto' G
         val texp = Inject.clean texp
         fun join f (G, x) = (G, f x)
         fun map_self (G, []) = (G, [])
           | map_self (G, h::t) =
                 let val (G, h) = substExtypevarNoAuto' G h
                     val (G, t) = map_self (G, t)
                 in
                   (G, h::t)
                 end
         fun pair_self (A, B) =
            let val (G, A) = substExtypevarNoAuto' G A
                val (G, B) = substExtypevarNoAuto' G B
            in
              (G, (A, B))
            end
     in
        case texp of
            Typevar tv => (G, Typevar tv)
        | Extypevar tv =>
              D.modEx tv
                    (*fFound=*)  (fn (var', info') => let in case info' of
                                                 UnknownEx => ([D.ExType (var', info')], Extypevar tv)
                                               | SolvedEx A => ([D.ExType (var', info')], A)
                                               | SectEx A  => ([D.ExType (var', info')], Extypevar tv)
                                               | UnionEx A => ([D.ExType (var', info')], Extypevar tv)
                                          end)
                    (*fNotFound=*) (fn () => ([], Extypevar tv))
                    G
      
      | All(tv, uu, texp) => join (fn texp => All(tv, uu, texp)) (self texp)
      | Tycon (tc, index, texps) => join (fn texps => Tycon(tc, index, texps)) (map_self (G, texps))
      | Arrow(d, cod) => join (fn (d, cod) => Arrow(d, cod)) (pair_self (d, cod))
      | Product texps => join (fn texps => Product texps) (map_self (G, texps))
      | Sect(A, B) => join (fn (A, B) => Sect(A, B)) (pair_self (A, B))
      | Union(A, B) => join (fn (A, B) => Union(A, B)) (pair_self (A, B))
      | Rsect(A, B) => join (fn (A, B) => Rsect(A, B)) (pair_self (A, B))
      | Runion(A, B) => join (fn (A, B) => Runion(A, B)) (pair_self (A, B))
      | Univ(a, sort, texp) => join (fn texp => Univ(a, sort, texp)) (self texp)
      | Exis(a, sort, texp) => join (fn texp => Exis(a, sort, texp)) (self texp)
      | Top => (G, Top)
      | Bot => (G, Bot)
      | Record(fld, A) => join (fn A => Record(fld, A)) (self A)
      | Implies(P, A) => join (fn A => Implies(P, A)) (self A)
      | Conj(P, A) => join (fn A => Conj(P, A)) (self A)
   end

 fun substExtypevarNoAuto mctx A =
    let val (G, A) = substExtypevarNoAuto' (getG mctx) A
    in
         A
    end


  (* WARNING: not capture-avoiding
 *)
  fun substExtypevarAuto' G texp =
     let val self = substExtypevarAuto' G
         val texp = Inject.clean texp
         fun join f (G, x) = (G, f x)
         fun map_self (G, []) = (G, [])
           | map_self (G, h::t) =
                 let val (G, h) = substExtypevarAuto' G h
                     val (G, t) = map_self (G, t)
                 in
                   (G, h::t)
                 end
         fun pair_self (A, B) =
            let val (G, A) = substExtypevarAuto' G A
                val (G, B) = substExtypevarAuto' G B
            in
              (G, (A, B))
            end
     in
        case texp of
            Typevar tv => (G, Typevar tv)
        | Extypevar tv =>
              D.modEx tv
                    (*fFound=*)  (fn (var', info') => let in case info' of
                                                 UnknownEx => ([D.ExType (var', info')], Extypevar tv)
                                               | SolvedEx A => ([D.ExType (var', info')], A)
                                               | SectEx A  => ([D.ExType (var', SolvedEx A)], A)
                                               | UnionEx A => ([D.ExType (var', SolvedEx A)], A)
                                          end)
                    (*fNotFound=*) (fn () => ([], Extypevar tv))
                    G
      
      | All(tv, uu, texp) => join (fn texp => All(tv, uu, texp)) (self texp)
      | Tycon (tc, index, texps) => join (fn texps => Tycon(tc, index, texps)) (map_self (G, texps))
      | Arrow(d, cod) => join (fn (d, cod) => Arrow(d, cod)) (pair_self (d, cod))
      | Product texps => join (fn texps => Product texps) (map_self (G, texps))
      | Sect(A, B) => join (fn (A, B) => Sect(A, B)) (pair_self (A, B))
      | Union(A, B) => join (fn (A, B) => Union(A, B)) (pair_self (A, B))
      | Rsect(A, B) => join (fn (A, B) => Rsect(A, B)) (pair_self (A, B))
      | Runion(A, B) => join (fn (A, B) => Runion(A, B)) (pair_self (A, B))
      | Univ(a, sort, texp) => join (fn texp => Univ(a, sort, texp)) (self texp)
      | Exis(a, sort, texp) => join (fn texp => Exis(a, sort, texp)) (self texp)
      | Top => (G, Top)
      | Bot => (G, Bot)
      | Record(fld, A) => join (fn A => Record(fld, A)) (self A)
      | Implies(P, A) => join (fn A => Implies(P, A)) (self A)
      | Conj(P, A) => join (fn A => Conj(P, A)) (self A)
   end

 fun substExtypevarAuto mctx t =
    let val (G, t) = substExtypevarAuto' (getG mctx) t
    in
      (updateG mctx (fn _ => G),   t)
    end

(*
  fun replaceExinfo tv newinfo ctxt =
    case ctxt of
      Empty => fail ("replaceExinfo: asked to replace existential " ^ extv2str tv ^ " not in extypes")
    | Ctx(tv', info, ctxt) =>
        if tv = tv' then Ctx(tv, newinfo, ctxt)
        else Ctx(tv', info, replaceExinfo tv newinfo ctxt)
*)


  fun solveExtype WHO mctx tv infoFn =
      let val _ = dprint (fn () => "solveExtype " ^ WHO ^ ": " ^ tv2str tv
                             (* ^ D.toString (D.ExType(tv, infoFn)) *))
          val mctx = updateG mctx (fn G => D.setEx tv infoFn G)
      in
(*        print ("solved, yielding mctx EXTYPES: " ^ extypesToString (getExtypes mctx) ^ "\n"); *)
          mctx
      end

  fun solveExtypeArtic mctx tv newvars solution =
      let (* val _ = print ("solveExtype " ^ extv2str tv ^ " := " ^ t2str solution ^ "\n") *)
        val mctx = updateG mctx (D.setExArtic
                                                    tv
                                                    (List.map (fn tv => (tv, UnknownEx)) newvars)
                                                    solution)
      in
(*          print ("solved, yielding mctx EXTYPES: " ^ extypesToString (getExtypes mctx) ^ "\n");
*)
          mctx
      end



  fun applyExtypesINFORMATIONAL (G, texp) =
    Types.substExtypevar (D.exToAssoc G) texp
  
  fun applyExtypes (G, texp) =
    substExtypevarAuto' G texp
  
  fun unsolvedExtypevars mctx =
    case D.unsolvedExtypevarsAux (getG mctx) of
      [] => false
    | _::_ => true
  
  fun applyEx (mctx, texp) =
    let val (G, texp) = applyExtypes (getG mctx, texp)
    in
      (updateG mctx (fn _ => G),  texp)
    end

  fun getExFromG G tv =
    case G of
      [] => raise Option
    | (d as D.ExType (var', info')) :: rest =>
        if tv = var' then
            info'
        else getExFromG rest tv
    | d :: rest =>
        getExFromG rest tv

  fun getEx mctx tv = getExFromG (getG mctx) tv
  fun isUnionEx mctx tv = case getEx mctx tv of UnionEx _ => true | _ => false
  fun isSectEx mctx tv = case getEx mctx tv of SectEx _ => true | _ => false

  fun t2str' mctx texp =
    t2str (applyExtypesINFORMATIONAL (getG mctx, texp))

  fun replaceVarInfo var info ctxt =
      case ctxt of
          Empty => Empty
        | Ctx(var', info', ctxt') =>
              if var = var' then
                Ctx(var', info, ctxt')    (* Assumes var does not appear more than once *)
              else
                Ctx(var', info', replaceVarInfo var info ctxt')

  fun modifyInfo var modifier ctxt =
      case ctxt of
          Empty => Empty
        | Ctx(var', info', ctxt') =>
              if var = var' then
                Ctx(var', modifier info', ctxt')    (* Assumes var does not appear more than once *)
              else
                Ctx(var', info', modifyInfo var modifier ctxt')

  fun typeinfoToString tc (Typeinfo{indexsort, parameters, elabTypedecs}) =
    SOME (TC.toString tc ^ " : Typeinfo{"
        ^ X.Sorting.toString indexsort
        ^ ", ..."
(*        ^ ", elabTypedecs" *)
        ^ "}\n")
  
  fun rctxToString (RCTX{con, types, distinguished, functions}) =
      let fun maybePrint name f Empty = ""
            | maybePrint name f (ctxt as Ctx _) = "--" ^ name ^ ":\n" ^ f ctxt  ^ "\n"
      in
        maybePrint "constructors" (ctxtToString conToString) con
     ^ maybePrint "types" (ctxtToString typeinfoToString) types
      end

  fun mctxToString (MCTX{G= G, index, path, state, constraint, varmap}) =
         "--G: " ^ D.GammaToString (checkG G)
(*      "--path info:\n" ^ pathToString path ^ "\n" *)
(*      ^ "--varmap:\n" ^ Renaming.toString varmap ^ "\n" *)
      ^ "--index context:\n" ^ indexToString index ^ "\n"
(*      ^ "--high constraint:\n" ^ X.Constraint.toString constraint ^ "\n" *)
      ^ "--low constraint:\n" ^ (case state of
                                     NONE => "inconsistent"
                                   | SOME (state, djs) => Solve.stateToString state ^ ", <<djs>>\n")

  fun mapvarMctx mctx a =
      Renaming.apply (getVarmap mctx) a

  fun compVarmap mctx varmap =
      updateVarmap mctx (fn oldVarmap => Renaming.compose oldVarmap varmap)

  fun ctxToString (rctx, mctx) =
      rctxToString rctx ^ mctxToString mctx

  fun trackToString (TRK (pattern, A, ctx as (rctx, mctx))) =
    "TRK (" ^ P.p P.printPat pattern ^ ", dom= " ^ t2str A (* ^ ", " ^ mctxToString mctx *) ^ ")"

  fun tracksToString trks =
    Separate.list "\n" (List.map trackToString trks) ^ "\n"

  fun otrkToString (OTRK (pattern, c, assumptions, (domain, codomain), ctx)) =
        "OTRK("
      ^ (fn SOME p0 => P.p P.printPat p0 | NONE => "") pattern
       ^ ",  " ^ Renaming.toString assumptions
      ^ ".  " ^ t2str domain
      ^ " --> " ^ t2str codomain
      ^  ", ...)"

  fun otrksToString trks =
    Separate.list "\n" (List.map otrkToString trks) ^ "\n"


  fun eq_mctx (mctx1 as MCTX{G= G1, index= index1, constraint= constraint1, state= state1, path= path1, varmap= varmap1},
               mctx2 as MCTX{G= G2, index= index2, constraint= constraint2, state= state2, path= path2, varmap= varmap2})
      info
      =
      let (* val _ = print ("eq_mctx: mctx1 = <<" ^ mctxToString mctx1
                         ^ "\n>>  mctx2 = << " ^ mctxToString mctx2
                         ^ "\n")     *)
      in
case
      compose info (eq_list eq_indexassumption (index1, index2))
         (eq_constraint (constraint1, constraint2))
(*      andalso
      true   (* state *)
      andalso
      true   (* path *)
  andalso
??????? XXX       fn info => if D.eqG (G1, G2) then SOME info else NONE
*)
  of 
      NONE => ((*print "eq_mctx _FAIL_\n"; *)NONE)
    | SOME x => ((*print "eq_mctx _SUCC_\n"; *)SOME x)
end

  fun eq_ctx (ctx1 as (rctx1, mctx1), ctx2 as (rctx2, mctx2)) info =
      let (* val _ = print ("eq_ctx: <<" ^ ctxToString ctx1
                         ^ "\n>>  ctx2 = << " ^ ctxToString ctx2
                         ^ "\n")
*)
      in
          compose info (eq_rctx (rctx1, rctx2))
            (eq_mctx (mctx1, mctx2))
      end

  fun renameIndex s (X.Uvar v) = X.Uvar (Renaming.apply s v)
    | renameIndex s (X.Evar v) = X.Evar (Renaming.apply s v)
    | renameIndex s (X.Nil sym) = X.Nil sym
    | renameIndex s (X.App (f, obj)) = X.App (f, renameIndex s obj)
    | renameIndex s (X.Tuple objs) = X.Tuple (map (renameIndex s) objs)
    | renameIndex s (X.Proj (n, obj)) = X.Proj (n, renameIndex s obj)
    | renameIndex s (X.Literal stuff) = X.Literal stuff
    | renameIndex s (X.True) = X.True
    | renameIndex s (X.False) = X.False
    | renameIndex s (X.NODIM) = X.NODIM
    | renameIndex s (X.BaseDim sym) = X.BaseDim sym

  fun renameConstraint s W = case W of
      X.EQ(sort, e1, e2) => X.EQ(sort, renameIndex s e1, renameIndex s e2)
    | X.PRED(sym, exp) => X.PRED(sym, renameIndex s exp)
    | X.TRUE => X.TRUE
    | X.AND(W1, W2) => X.AND(renameConstraint s W1, renameConstraint s W2)
    | X.OR(W1, W2) => X.OR(renameConstraint s W1, renameConstraint s W2)
    | X.IMPLIES(W1, W2) => X.IMPLIES(renameConstraint s W1, renameConstraint s W2)
    | X.ALL(a, sort, W0) => X.ALL(Renaming.apply s a, sort(*XXX*), renameConstraint s W0)
    | X.EXISTS(a, sort, W0) => X.EXISTS(Renaming.apply s a, sort(*XXX*), renameConstraint s W0)

  fun renameRecord s record = case record of
      X.N => X.N
    | X.O i => X.O (renameIndex s i)
    | X.I fields => X.I (List.map (fn (fieldname, i) => (fieldname, renameIndex s i)) fields)
  
  fun rename s texp =
      case texp of
          Arrow(A1, A2) => Arrow(rename s A1, rename s A2)
        | Typevar tv => Typevar tv
        | Extypevar tv => Extypevar tv
        | All(tv, uu, A) => All(tv, uu, rename s A)
        | Product(As) => Product(map (rename s) As)
        | Tycon(tc, record, texps) => Tycon(tc, renameRecord s record, map (rename s) texps)
        | Sect(A1, A2) => Sect(rename s A1, rename s A2)
        | Union(A1, A2) => Union(rename s A1, rename s A2)
        | Rsect(A1, A2) => Rsect(rename s A1, rename s A2)
        | Runion(A1, A2) => Runion(rename s A1, rename s A2)
        | Univ(a, sort, A0) => Univ(Renaming.apply s a, sort(*XXX*), rename s A0)
        | Exis(a, sort, A0) => Exis(Renaming.apply s a, sort(*XXX*), rename s A0)
        | Top => Top
        | Bot => Bot
        | Record(fld, A0) => Record(fld, rename s A0)
        | Implies(W0, A0) => Implies(renameConstraint s W0, rename s A0)
        | Conj(W0, A0) => Conj(renameConstraint s W0, rename s A0)

  fun renameIndexAssn s assn = case assn of
      Iall(sym, sort) => Iall(Renaming.apply s sym, sort(*XXX*))
    | Iexists(sym, sort) => Iexists(Renaming.apply s sym, sort(*XXX*))
    | Prop P => Prop (renameConstraint s P)
    | Barrier id => Barrier id

  fun renameMctx s (MCTX{G= G, index : indexassumption list       (* Index environment *)
       , constraint
       , state : (state * disjuncts) option      (* Solver state (NONE means inconsistent) *)
       , path
       , varmap}) =
      let val index' = map (renameIndexAssn s) index
          val constraint' = renameConstraint s constraint
          val state' = (* Option.map (fn state => Solve.addVarmap state s) state *) state
      in
          MCTX{G= G, index= index', constraint= constraint', state= state', path= path,
               varmap= varmap}
      end

  fun sortOK sort = case sort of
     X.Subset _ =>
           let in
               (*print "<<SUBSET>>"; *) ()
           end
   | _ => ()
  
  fun addUniversal (mctx, (a, sort)) : mctx =
      let val Iall(a, sort) = renameIndexAssn (getVarmap mctx) (Iall(a, sort))
          val mctx = updateIndex mctx (fn index => Iall(a, sort) :: index)
      in
          sortOK sort;
          dprint (fn () => "Context.%% Iall(" ^ IndexSym.toString a ^ ") : " ^ Indexing.Sort.toString sort);
          mapUpdateState mctx (fn (state, djs) =>
                                  case Solve.addUniversalAssn state (mapvarMctx mctx a, sort) of
                                    NONE => NONE
                                  | SOME state => SOME (state, djs))
      end

  fun %% (mctx, indexassn) =
      case indexassn of
          Prop X.TRUE => [mctx]
        | _ => 
              let val indexassn = renameIndexAssn (getVarmap mctx) indexassn
                  val mctx = updateIndex mctx (fn index => indexassn :: index)
                  val mctxes = case indexassn of

                      Iall(a, sort) =>
                          let in 
                            sortOK sort;
                            dprint (fn () => "Context.%% Iall(" ^ IndexSym.toString a ^ ") : " ^ Indexing.Sort.toString sort);
                            [mapUpdateState mctx 
                                            (fn (state, djs) =>
                                                case Solve.addUniversalAssn state (mapvarMctx mctx a, sort) of
                                                    SOME newState => SOME (newState, djs)
                                                  | NONE => (dprnt "Context.%% Iall NONE\n"; NONE)
                                            )
                            ]
                          end

                    | Iexists(a, sort) =>
                          let in 
                            sortOK sort;
                            dprint (fn () => "Context.%% Iexists(" ^ IndexSym.toString a ^ ") : " ^ Indexing.Sort.toString sort);
                            [mapUpdateState mctx 
                                            (fn (state, djs) =>
                                                case Solve.addExistentialAssn state (mapvarMctx mctx a, sort) of
                                                    SOME newState => SOME (newState, djs)
                                                  | NONE => (dprnt "Context.%% Iexists NONE\n"; NONE)
                                            )
                            ]
                          end

                    | Prop P =>                  
(*                          splayMapUpdateState mctx (fn state =>
                                                 let in case state of NONE => []
                                                  | SOME (state, djs) =>
                                                        let in case Solve.assume (state, renameConstraint (getVarmap mctx) P) of
                                                            NONE => []
                                                          | SOME (state, djs2) =>  [ Solve.takeAlong djs2 (state, djs) ]
                                                        end
                                                 end)
*)
                            [mapUpdateState mctx 
                                            (fn (state, djs) =>
                                                case Solve.assume (state, renameConstraint (getVarmap mctx) P) of
                                                    SOME (newState, djs) => SOME (newState, djs)
                                                  | NONE => (dprnt "Context.%% Prop NONE\n"; NONE)
                                            )
                            ]

                    | Barrier b_id =>
                         [ updateConstraint (mapUpdateState mctx
                                            (fn (state, djs) =>
                                             let val (newState, W) = Solve.ejectConstraint state
                                             in
                                                 SOME (newState, djs)
                                             end))
                            (fn _ => X.TRUE) ]
              in
                  mctxes
              end
  infix 5 %%
  
  fun forceSingleton [x] = x
    | forceSingleton _ = raise Match
  
  fun applyMctx (rctx, mctx) operator secondArgument =
    (rctx, forceSingleton (operator (mctx, secondArgument)))
  
  fun $+ (mctx, crumb) =
      let val _ = dprint (fn () => "$+ " ^ crumbToString crumb ^ "")
      in
          updatePath mctx (fn path => crumb :: path)
      end
  infix 5 $+
  
  fun $- (mctx) = updatePath mctx List.tl
  
  fun ++ (mctx, (pv,texp)) = updateG mctx (D.addOrdinary (pv, (texp, Uservar)))
  infix 5 ++
  
  fun +- (mctx, (pv, (texp, elabOpt))) = updateG mctx (D.addLinear (pv, (texp, elabOpt)))
  infix 5 +-
  
  fun +--+ (mctx, (tv, texpopt)) = updateG mctx (D.addUnivType (tv, texpopt))
  infix 5 +--+
  
  fun +--+= (mctx, (tv, newTexpopt)) =
    let val _  = PRINT ("+--+= mctx= " ^ mctxToString mctx ^ "\n")
       val _ = PRINT ("+--+= tv= " ^ tv2str tv ^ topt2str " := " newTexpopt ^ "\n")
       val mctx = updateG mctx (D.setUnivType tv newTexpopt)
       val _  = PRINT ("+--+= updated mctx= " ^ mctxToString mctx ^ "\n")
    in
       print (mctxToString mctx ^ "\n");
       mctx
    end
  infix 5 +--+=

  fun +~~+ (mctx, (pv, (locexp, pexp))) = updateG mctx (D.addSlack(pv, (locexp, pexp)))
  infix 5 +~~+

  fun addConinfo rctx (pv,contype) = updateCon rctx (fn con => Ctx(pv, contype, con))

(*
  fun addTypeinfo (rctx, (tc, typeinfo)) =
      let val rctx = 
              updateTypes rctx
                  (fn types =>
                      let val _ = print ("addTypeinfo: old=" ^ Int.toString (ctxtlength types) ^ "\n")
                      in
                          Ctx(tc, typeinfo, types)
                      end)
      in
          print ("addTypeinfo: new=" ^ Int.toString (ctxtlength (getTypes rctx)) ^ "\n");
          rctx
      end
*)
  fun addTypeinfo (rctx, (tc, typeinfo)) =
              updateTypes rctx
                  (fn types =>
                      Ctx(tc, typeinfo, types))

  fun findOwner ctxt conjunct = case ctxt of
                  Empty => raise LookupFailure (fn () => "getConjunctOwner")
                | Ctx (owner, Coninfo{conjuncts, ...}, rest) =>
                      if List.exists (fn (conjunct', _) => conjunct' = conjunct) conjuncts then
                          owner
                      else
                          findOwner rest conjunct

  fun getConjunctOwner rctx conjunct =
      findOwner (getCon rctx) conjunct

  fun findConjunctType ctxt conjunct = case ctxt of
                  Empty => raise LookupFailure (fn () => "getConjunctType")
                | Ctx (owner, Coninfo{conjuncts, ...}, rest) =>
                      let in case Assoc.getOpt conjuncts conjunct of
                                 SOME texp => texp
                              | NONE =>
                                   findConjunctType rest conjunct
                      end

  fun getConjunctType rctx conjunct =
      findConjunctType (getCon rctx) conjunct


  fun empty_rctx (primtcs, distinguished, functions) =
       foldl (fn ((tc, sorting), rctx) =>
                 addTypeinfo(rctx, (tc, Typeinfo{indexsort= sorting,
                                                  parameters= [], (* XXX : will need to change this if any primitive types are polymorphic *)
                                                  elabTypedecs= []}
             )))
       (RCTX{
          types= Empty,
          con= Empty,
          distinguished= distinguished,
          functions= functions
          })
      primtcs

  fun empty_mctx () =
      MCTX{G= D.empty,
          index= [],
          path= [],
          state= SOME (Solve.empty(), []),
          constraint= X.TRUE,
          varmap= Renaming.empty
      }


(* empty_ctx : unit -> (rctx * mctx)    ---For interactive use ONLY; has nonsense symbols *)
  fun empty_ctx () =
     (empty_rctx ([],
                  {exnTC= TC.fromInt 0,
                   intTC=TC.fromInt 1,
                   stringTC=TC.fromInt 2,
                   sumTC= TC.fromInt 3,
                   inl_pv = PV.fromInt 111,
                   inr_pv = PV.fromInt 222},
                 {exit= PV.fromInt 0,
                 elab_Bot= PV.fromInt 0}),
      empty_mctx ())


  fun noUnks' domain info mctx W =
      case X.Constraint.freeVars domain W of
          [] => ()
        | vars => (print ("noUnks (" ^ info ^ "): unknown variables in W;\n variables = {" ^ Separate.list ", " (map (IndexSym.toString) vars) ^ "},\n "
                          ^ " W = " ^ X.Constraint.toString W ^ "\n");
                   raise Option)

  fun noUnks info mctx W =
      noUnks' (domain (getIndex mctx)) info mctx W

  fun noUnksType info mctx outerA =
      let val index = getIndex mctx
          val varmap = getVarmap mctx
          val outerA = rename varmap outerA
          val d = domain index
          fun checkIndex d i =
              case X.freeVars d i of
                  [] => ()
                | vars => (print ("noUnksType (" ^ info ^ "): unknown variables in i;\n variables = {" ^ Separate.list ", " (map (IndexSym.toString) vars) ^ "},\n "
                                  ^ " outerA (renamed) = " ^ t2str outerA ^ "\n");
                           raise Option)
          
          fun ff d A =
              let val f = ff d in
                  case A of
                      Arrow(A1, A2) => (f A1; f A2)
                    | Typevar tv => ()
                    | Extypevar tv => ()
                    | All(tv, uu, A) => f A
                    | Product As => List.app f As
                    | Tycon (tc, record, texps) =>
                        (X.app_record (checkIndex d) record;
                         List.app f texps)
                    | Sect(A1, A2) => (f A1; f A2)
                    | Union(A1, A2) => (f A1;f A2)
                    | Rsect(A1, A2) => (f A1; f A2)
                    | Runion(A1, A2) => (f A1;f A2)
                    | Univ(a, sort, A0) => ff (a :: d) A0
                    | Exis(a, sort, A0) => ff (a :: d) A0
                    | Top => ()
                    | Bot => ()
                    | Record(fld, A) => f A
                    | Implies(P, A) => (noUnks' d info mctx P;
                                        f A)
                    | Conj(P, A) => (noUnks' d info mctx P;
                                        f A)
              end
      in
          ff d outerA
      end


(*  %%%%, &&&,  &&, quantifyUpToBarrier
*)
  fun %%%% failure (mctx, indexassn) k =
    case mctx %% indexassn of
        [result] => let in case getState result of
                              NONE => raise_Dead failure result (fn () => "%%%%")
                           | SOME _ => k result
                          end

  fun yellDjs mctx =
      case getState mctx of
          SOME (_, x :: _) => print ("yellDjs\n")
        | _ => ()

  fun &&& failure (mctx, W) k =
      let
          val state = getState mctx
          val index = getIndex mctx
          val _ = noUnks "&&&" mctx W
      in
        case state of
            NONE => raise_Dead failure mctx (fn () => "Prevailing inconsistency noticed (&&&)")
          | SOME (state, _) =>
                let 
                    val  _ = dprint (fn () => "#  &&&: " ^ mctxToString mctx ^ " +++ \n" ^ X.Constraint.toString W)
                in
                    case Solve.accumulate (state, W) of
                        NONE => (dprnt "&&&: INCONSISTENT";
                                 raise_Dead failure mctx (fn () => "Inconsistency detected (&&&)"))
                      | SOME (result, djs) =>
                            let val _ = case djs of [] => () | _ => print ("&&&: djs not empty\n")
                                fun stateToMctx newState =
                                    let val mctx = updateState mctx (Option.map (fn (_, djs0) => Solve.takeAlong djs0 (newState, djs)))
                                        val mctx = updateConstraint mctx (fn constraint => X.mkAND(constraint, W))
                                        val _ = yellDjs mctx
                                    in
                                        mctx
                                    end
                            in
                                k (stateToMctx result)
                            end
                end
    end

  fun && failure (mctx, W) k =
      let val W = renameConstraint (getVarmap mctx) W
      in
          &&& failure (mctx, W) k
      end

  exception QuantifyBarrierFault of Barrier.id * Barrier.id
  
  fun quantify state cutoff index W =
      let fun quant [] W =
              let in
                  case cutoff of
                      NONE => ([], W)
                    | SOME _ => raise Option    (* cutoff not found! *)
              end
            | quant (Prop P :: index) W = quant index (X.mkIMPLIES(P, W))
            | quant (Iall(sym,sort) :: index) W = quant index (X.ALL(sym, sort, W))
            | quant (Iexists(sym,sort) :: index) W =
let (*  val _ = print ("## " ^ IndexSym.toString sym ^ "\n")
    val _ = print ("## " ^ X.Constraint.toString W ^ "\n")
    val _ = print ("###### EXISUB-STATE   " ^ Solve.stateToString state ^ "\n\n")
    val _ = print ("## " ^ " -------> \n") *)
in
                 quant index (if !r_forceElim then
(let val result = 
                                 #2 (Solve.forceElimExistential state (X.EXISTS(sym, sort, W)))
    val _ = dprint (fn () => "## " ^ X.Constraint.toString result)
in result end)
else (X.EXISTS(sym, sort, W)))
end
            | quant (Barrier id :: index) W =
                    let in case cutoff of 
                        SOME id' => if id'=id then (index, W)   (* barrier ID matches, cut off now *)
                                    else quant index W
                      | NONE => quant index W
                    end
      in
          quant index W
      end

  fun quantify_full state index W =
      case quantify state NONE index W of
          ([], W') => W'
        | (_, W') => raise Match
(*
                      fun onlyMInfer (MInfer stuff) = SOME stuff
                        | onlyMInfer _ = NONE

                      fun onlyMCheck (MCheck stuff) = SOME stuff
                        | onlyMCheck _ = NONE

                      fun onlyMSubtype (MSubtype stuff) = SOME stuff
                        | onlyMSubtype _ = NONE


                      fun search eqf key pairs =
                          case pairs of 
                              [] => NONE
                        | ((key', value') :: others) =>
                          let in case eqf (key, key') of
                              NONE => search eqf key others
                            | SOME info => SOME (key', value', info)
                          end

                      fun memoSubtype (ctx, left, right) memoList =
                          let val msubs = List.mapPartial onlyMSubtype memoList
                              val result =
                                  search (fn ((ctx1, left1, right1), (ctx2, left2, right2)) =>
                                          composeList [] [eq_texp (left1, left2),
                                                          eq_texp (right1, right2),
                                                          eq_ctx (ctx1, ctx2)])
                                  (ctx, left, right)
                                  msubs
                          in
                              Option.map (fn ((ctx, left, right), ctxOpt, info) =>
                                          let in case ctxOpt of NONE => NONE
                                        | SOME stuff => SOME (stuff, info) end) result
                          end

                      fun memoInfer (inference_disposition, ctx) memoList =
                          let val minfers = List.mapPartial onlyMInfer memoList
                          in
                              search (fn ((inf1, ctx1), (inf2, ctx2)) =>
                                      if inf1 <> inf2 then NONE
                                      else eq_ctx (ctx1, ctx2) [])
                              (inference_disposition, ctx)
                              minfers
                          end

                      fun memoCheck (ctx, texp) memoList =
                          let val _ = INC "memoLookup" memoLookup
                              val mchecks = List.mapPartial onlyMCheck memoList
                              val result =
                                  search (fn ((ctx1, texp1), (ctx2, texp2)) =>
                                          compose [] (eq_texp (texp1, texp2)) (eq_ctx (ctx1, ctx2)))
                                  (ctx, texp)
                                  mchecks
                          in
                              Option.map (fn ((ctx, texp), ctxes, info) =>
                    (                 pprint ((fn () => "@@@LOL MATCH  " ^ ctxToString ctx ^ "\n"));

                                          (ctxes, info))) result
                          end
                      val memoCheck = (memoCheck
                          : (ctx * texp) -> memoinfo list
                          -> (ctx list * (infon list)) option)
                         (* symsym list: renaming: FROM argument ctx's variables TO returned ctx's variables *)
*)

(* for all a in rctx.
   [originalMctx.varmap] a  in FV(originalMctx)
   [mctx.varmap] a  in FV(mctx)
*)
  fun quantifyUpToBarrier failure originalMctx mctx barrier_id k =
      let val originalMctxVarmap = getVarmap originalMctx
          val varmap = getVarmap mctx
          val _ = dprnt ("quantifyUpToBarrier")
          val _ = dprint (fn () => "    originalMctx = " ^ mctxToString originalMctx)
          val _ = dprint (fn () => "    mctx = " ^ mctxToString mctx)
          val _ = dprint (fn () => "    barrier_id = " ^ Barrier.toString barrier_id)
          val mctx = renameMctx (Renaming.inverse varmap) mctx   (* Reverse the map, yielding an mctx in terms of whatever rctx we have *)
          val mctx = renameMctx originalMctxVarmap mctx   (* Put mctx into the same language as originalMctx *)
          val constraint = getConstraint mctx
      in
          case (getState originalMctx, getState mctx) of
              (NONE, _) => k originalMctx
            | (SOME _, NONE) => raise_Dead failure mctx (fn () => "quantifyUpToBarrier: inconsistency")
            | (SOME _, SOME (state, djs)) =>
                  let val (index', Wquant) = quantify state (SOME barrier_id) (getIndex mctx) constraint
                      val _ = dprint (fn () => "*** index' = " ^ indexToString index')
                      val _ = dprint (fn () => "*** Wquant = " ^ X.Constraint.toString Wquant)
                  in
                      (noUnks "quantifyUpToBarrier" originalMctx Wquant;
                       &&& failure (originalMctx, Wquant) k)
                  end
      end

  fun finalSubstLocexp mctx locexp =
      let
          val G = getG mctx
          val _ = dprint (fn () => "finalSubstLocexp using " ^ D.assocToString (D.exToAssoc G))
      in
          SdmlFold.fold_locexp (SdmlFold.texpSpec
                                   (fn A => applyExtypesINFORMATIONAL (G, A)))
                                   locexp
      end

  fun hasExtypevars mctx =
      false (* XXX *)

  fun isSolved (rctx, mctx as MCTX{G, index, ...}) =
      solve mctx
      andalso
      not (hasExtypevars mctx)


  type point = Solve.point

  fun isPristine (mctx as MCTX{G, index, ...}) =
      List.null index
      andalso
      not (hasExtypevars mctx)

  fun push (mctx as MCTX{state= NONE, ...}) = (mctx, 0)

    | push (mctx as MCTX{state= SOME(state, disjuncts), ...}) =
         let val (state', point) = Solve.push state
         in
             (mapUpdateState mctx (fn _ => SOME(state', disjuncts)),
              point)
         end

   fun popto (mctx, point) =
       mapUpdateState mctx
         (fn (state, disjuncts) =>
             SOME (Solve.popto (state, point),
                   disjuncts))

end
