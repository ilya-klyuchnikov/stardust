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
(* File: Sdml.sml
 * Author: Joshua Dunfield
 *)

signature SDML = sig
  type  pv = PV.sym
  type  tc = TC.sym
  type  tv = TV.sym
  
  type ('a, 'b) fixitem = {item: 'a, fixity: 'b option, loc: Location.location}
  
  type universe = Types.universe

  structure Variance : sig
      datatype t =
        Non | Co | Contra
      
      val toString : t -> string   (* "Non" | "Co" | "Contra" *)
      val toDeclString : t -> string  (* "", "+", "-" *)
  end
  
  datatype texp =
      Typevar of tv
    | Extypevar of tv
    | All of tv * universe * texp
    
    | Arrow of texp * texp
    | Product of texp list
    | Tycon of tc * Indexing.record * texp list

    | Record of string * texp

    | Top
    | Bot          
    | Sect of texp * texp
    | Union of texp * texp

    | Rsect of texp * texp
    | Runion of texp * texp
    | Univ of IndexSym.sym * Indexing.sort * texp
    | Exis of IndexSym.sym * Indexing.sort * texp
    | Implies of Indexing.constraint * texp
    | Conj of Indexing.constraint * texp
  
(*  datatype tscm = Tscm of tv list * texp
*)
  
  datatype tvinfo = Tvinfo of tv * Variance.t
  
  datatype typedec =
      Datatype of {tc : tc,
                   builtin : bool,   (* built-in in target language? *)
                   params : tvinfo list,
                   sorting : Indexing.Sorting.t,
                   constructors : con list}
    | Synonym of {tc : tc, tv : tv, params : tv list, definition : texp}
  
  and con = Constructor of {c: pv, nullary: bool, basetype: texp, conjuncts: (pv * texp) list, elaborated_conjuncts: (pv * texp) list, contype: texp}
  
  val quantifyCtype : texp -> tvinfo list -> texp
  
  type typedecs = typedec list

  structure AnnotationType : sig   (* type, also with  "d >:>" ...  and  "some a:sort." *)
     datatype t =
              Type of texp
            | LeftProgramVar of pv * texp * t
(*            | LeftIndexVar of pv * texp * t *)   (* unimplemented *)
            | Some of IndexSym.sym * Indexing.sort * t
  end
  type annotype = AnnotationType.t
  
  structure ConcreteContext : sig  (* Recommended abbreviation: CC *)
    datatype elem =
        IndexVar of IndexSym.sym * Indexing.sort
      | ProgramVar of pv * texp
      | TypeVar of tv
    
    (* WARNING:  Not capture-avoiding! *)
    val substIndex : (IndexSym.sym * Indexing.exp) list -> elem list -> elem list
    val substTypevar : (TV.sym * texp) list -> elem list -> elem list
    
    val shift : elem list -> elem list
  end
  
  type concrete_ctxt = ConcreteContext.elem list
  type typing = concrete_ctxt * texp
  
  type annotation = annotype list

  val just : texp -> annotation
  
  structure Dectype : sig
    datatype dectype =
        AGAINST of annotation
      | TOPLEVEL_AGAINST of texp
      | TOPLEVEL_NOT of texp
  end
  
  type locexp (* = Location.location * exp *)
  type locdec (* = Location.location * dec *)
  
  type spystuff = unit
  
  datatype dec_keyword = ValKW | FunKW

  datatype testsubtype_sense = IsSubtype | IsNotSubtype | MutualSubtypes

  datatype leftanno =
           LeftProgramVar of pv  * texp
  
  datatype dec =
        Dec of pv * dec_keyword * locexp
      | Typedec of typedecs
      | ValType of pv * Dectype.dectype
      | Datacon of pv * texp
      | TyvarVariance of tv * Variance.t
      | DatatypeWith of tc * Indexing.Sorting.t
      | Local of locdec list list * locdec list list

      | TestSubtype of testsubtype_sense * (texp * texp)
  
  and exp =
        Const of texp * string
      | Var   of pv
      | Con  of pv
      | Case  of locexp * arm list
      | Fn   of pv * locexp
      | App   of locexp * locexp
      | Conapp of pv * locexp
      | RecordExp  of string * locexp
      | Tuple  of locexp list
      | Merge of locexp list
      | Proj  of string * locexp
      | Let   of locdec list * locexp
      | Lethint of annotation * locexp
      | Anno  of locexp * annotation
      | LET   of pv * locexp * exp
      | LETSLACK of pv * locexp * exp
      | Lvar  of pv
      | Raise of locexp
      | Handle of locexp * pv * locexp   (* locexp1 handle pv => locexp2 *)
      | Spy of spystuff * locexp
      | Leftanno of leftanno * locexp
  
  and arm = Arm of pattern * locexp
  
  and pattern =
      VarPattern of pv
    | WildPattern
    | OrPattern of pattern list   (* OrPattern[]   means the empty pattern *)
    | CtorPattern of pv * pattern option
    | RecordPattern of string * pattern
    | TuplePattern of pattern list  (* TuplePattern[]  means  () *)
    | AsPattern of pv * pattern
    | StringPattern of string
    | IntPattern of int
  
  type decs = locdec list
  
  val getDectype : pv -> locdec list -> Dectype.dectype option

  structure Path : sig

    type 'a pexp (* = 'a * 'a exp *)

    datatype 'a dec =
        Dec of 'a pexp
      | Typedec
      | ValType
      | Datacon
      | TyvarVariance
      | DatatypeWith
      | TestSubtype

    and 'a exp =
          Const
        | Var
        | Con
        | Case of 'a pexp * 'a arm list
        | Fn of 'a pexp
        | App of 'a pexp * 'a pexp
        | Conapp of 'a pexp
        | RecordExp  of 'a pexp
        | Tuple  of 'a pexp list
        | Merge of 'a pexp list
        | Proj of 'a pexp
        | Let of 'a dec list * 'a pexp
        | Lethint of 'a pexp
        | Anno of 'a pexp
        | LET of 'a pexp * 'a pexp
        | LETSLACK of 'a pexp * 'a pexp
        | Lvar
        | Raise of 'a pexp
        | Handle of 'a pexp * 'a pexp
        | Spy of 'a pexp
        | Leftanno of 'a pexp

    and 'a arm = Arm of 'a pexp
  
  end

  type primopinfo =
       {source_texp : texp,
(*        target_texp : texp, *)
        proper_name : string,   (* e.g. "+"  *)
        sanitized_name : string,  (* e.g. "plus" *)
        elaboration : string}
  
  type distinguished = {exnTC : tc,
                        intTC : tc,
                        stringTC : tc,
                        sumTC : tc,
                        inl_pv : pv,
                        inr_pv : pv}
  
  datatype libinfo =
      Libinfo of {primtcs : (tc * Indexing.Sorting.t) list,
                  primops : (pv * primopinfo) list,
                  distinguished : distinguished}

  datatype program = Program of libinfo * decs * locexp
  
  val buildShadow : (unit -> 'a) -> exp -> 'a Path.pexp
  
  val isVal : exp -> bool
  val isSynth : exp -> bool

  val mkSect : texp * texp -> texp
  
  val patternToString : pattern -> string
  val patternOptionToString : pattern option -> string
end

structure Sdml : SDML = struct

  open Types
  
  type pv = PV.sym
  type tc = TC.sym
  type tv = TV.sym
  
  type ('a, 'b) fixitem = {item: 'a, fixity: 'b option, loc: Location.location}

  structure AnnotationType = struct
     datatype t =
              Type of texp
            | LeftProgramVar of pv * texp * t
(*            | LeftIndexVar of pv * texp * t *)   (* unimplemented *)
            | Some of IndexSym.sym * Indexing.sort * t
  end
  type annotype = AnnotationType.t

  fun just A = [AnnotationType.Type A]

  structure ConcreteContext = struct
    datatype elem = 
        IndexVar of IndexSym.sym * Indexing.sort
      | ProgramVar of pv * texp
      | TypeVar of tv

    fun substIndex assoc cc =
        case cc of
            [] => []
          | (IndexVar(a, sort) :: cc) => IndexVar(a, sort) :: (substIndex assoc cc)
          | (ProgramVar(pv, texp) :: cc) => ProgramVar(pv, Types.substIndex assoc texp) :: (substIndex assoc cc)
          | (TypeVar(tv) :: cc) => TypeVar(tv) :: (substIndex assoc cc)

    fun substTypevar assoc cc =
        case cc of
            [] => []
          | (IndexVar(a, sort) :: cc) => IndexVar(a, sort) :: (substTypevar assoc cc)
          | (ProgramVar(pv, texp) :: cc) => ProgramVar(pv, Types.substTypevar assoc texp) :: (substTypevar assoc cc)
          | (TypeVar tv :: cc) =>
              let in case Assoc.getOpt assoc tv of
                         NONE => TypeVar(tv) :: (substTypevar assoc cc)
                       | SOME _ => substTypevar assoc cc
              end

     fun shiftElem elem = case elem of 
       IndexVar(a, sort) => IndexVar(a, sort)
     | ProgramVar(pv, texp) => ProgramVar(pv, Types.shift_universe texp)
     | TypeVar tv => TypeVar tv

    val shift = List.map shiftElem
  end

  type concrete_ctxt = ConcreteContext.elem list
  type typing = concrete_ctxt * texp

  type annotation = annotype list

  structure Dectype = struct
    datatype dectype =
        AGAINST of annotation
      | TOPLEVEL_AGAINST of texp
      | TOPLEVEL_NOT of texp
  end

  type spystuff = unit

  datatype leftanno =
           LeftProgramVar of pv  * texp
  
  datatype dec_keyword = ValKW | FunKW
  datatype testsubtype_sense = IsSubtype | IsNotSubtype | MutualSubtypes
  datatype dec =
        Dec of pv * dec_keyword * locexp
      | Typedec of typedecs
      | ValType of pv * Dectype.dectype
      | Datacon of pv * texp
      | TyvarVariance of tv * Variance.t
      | DatatypeWith of tc * Indexing.Sorting.t
      | Local of locdec list list * locdec list list    (* thanks a lot, MLton! *)

      | TestSubtype of testsubtype_sense * (texp * texp)

  and exp =
        Const of texp * string
      | Var   of pv
      | Con  of pv
      | Case  of locexp * arm list (* arm list * locexp option *)
      | Fn   of pv * locexp
      | App   of locexp * locexp
      | Conapp of pv * locexp
      | RecordExp  of string * locexp
      | Tuple  of locexp list
      | Merge of locexp list
      | Proj  of string * locexp
      | Let   of locdec list * locexp
      | Lethint of annotation * locexp
      | Anno  of locexp * annotation
      | LET of pv * locexp * exp
      | LETSLACK of pv * locexp * exp
      | Lvar of pv
      | Raise of locexp
      | Handle of locexp * pv * locexp   (* locexp1 handle pv => locexp2 *)
      | Spy of spystuff * locexp
      | Leftanno of leftanno * locexp
    
  and arm = Arm of pattern * locexp
  
  and pattern =
      VarPattern of pv
    | WildPattern
    | OrPattern of pattern list   (* OrPattern[]   means the empty pattern *)
    | CtorPattern of pv * pattern option
    | RecordPattern of string * pattern
    | TuplePattern of pattern list  (* TuplePattern[]  means  () *)
    | AsPattern of pv * pattern
    | StringPattern of string
    | IntPattern of int

  withtype locexp = Location.location * exp
       and locdec = Location.location * dec

  type decs = locdec list

  fun getDectype pv [] = NONE
    | getDectype pv ((loc, dec) :: rest) = let in case dec of
                 ValType(pv', dectype) => if pv = pv' then SOME dectype else getDectype pv rest
               | _ => getDectype pv rest
               end

  structure Path = struct
    datatype 'a dec =
        Dec of 'a pexp
      | Typedec
      | ValType
      | Datacon
      | TyvarVariance
      | DatatypeWith
      | TestSubtype

    and 'a exp =
          Const
        | Var
        | Con
        | Case of 'a pexp * 'a arm list
        | Fn of 'a pexp
        | App of 'a pexp * 'a pexp
        | Conapp of 'a pexp
        | RecordExp  of 'a pexp
        | Tuple  of 'a pexp list
        | Merge of 'a pexp list
        | Proj of 'a pexp
        | Let of 'a dec list * 'a pexp
        | Lethint of 'a pexp
        | Anno of 'a pexp
        | LET of 'a pexp * 'a pexp
        | LETSLACK of 'a pexp * 'a pexp
        | Lvar
        | Raise of 'a pexp
        | Handle of 'a pexp * 'a pexp
        | Spy of 'a pexp
        | Leftanno of 'a pexp

    and 'a arm = Arm of 'a pexp
  
    withtype 'a pexp = 'a * 'a exp
  end

  type primopinfo =
       {source_texp : texp,
(*        target_texp : texp, *)
        proper_name : string,   (* e.g. "+"  *)
        sanitized_name : string,  (* e.g. "plus" *)
        elaboration : string}

    type distinguished = {exnTC : tc,
                        intTC : tc,
                        stringTC : tc,
                        sumTC : tc,
                        inl_pv : pv,
                        inr_pv : pv}
  
  datatype libinfo =
      Libinfo of {primtcs : (tc * Indexing.Sorting.t) list,
                  primops : (pv * primopinfo) list,
                  distinguished : distinguished}

  datatype program = Program of libinfo * decs * locexp

  fun buildShadow f exp =
    let fun glob exp = (f(), exp)

        fun build_locexp (loc, exp) = build exp
        and build exp =
            let val path =
                case exp of 
                    Const _ => Path.Const
                  | Var _ => Path.Var
                  | Con _ => Path.Con
                  | Case((loc, exp), arms) =>
                        Path.Case(build exp, map build_arm arms)
                  | Fn(_, (loc, exp)) =>
                        Path.Fn(build exp)
                  | App((loc1, exp1), (loc2, exp2)) => Path.App(build exp1, build exp2)
                  | Conapp(_, (loc, exp)) => Path.Conapp(build exp)
                  | RecordExp (_, locexp) => Path.RecordExp (build_locexp locexp)
                  | Merge locexps => Path.Merge (map build_locexp locexps)
                  | Tuple locexps => Path.Tuple (map build_locexp locexps)
                  | Proj(_, (loc, exp)) => Path.Proj (build exp)
                  | Let(decs, (loc, exp)) => Path.Let (map (fn (loc, dec) => build_dec dec) decs, build exp)
                  | Lethint(_, (loc, exp)) => Path.Lethint (build exp)
                  | Anno((loc, exp), _) => Path.Anno (build exp)
                  | LET(_, (loc1, exp1), exp2) => Path.LET(build exp1, build exp2)
                  | LETSLACK(_, (loc1, exp1), exp2) => Path.LETSLACK(build exp1, build exp2)
                  | Lvar _ => Path.Lvar
                  | Raise (loc, exp) => Path.Raise (build exp)
                  | Handle ((loc1, exp1), _, (loc2, exp2)) => Path.Handle (build exp1, build exp2)
                  | Spy (_, (loc, exp)) => Path.Spy (build exp)
                  | Leftanno (_, (loc, exp)) => Path.Leftanno (build exp)
            in
                glob path
            end
        and build_arm (Arm(_, (loc, exp))) = Path.Arm (build exp)
        and build_dec (Dec(_, _, (loc, exp))) = Path.Dec (build exp)
          | build_dec (Typedec _) = Path.Typedec
          | build_dec (ValType _) = Path.ValType
          | build_dec (Datacon _) = Path.Datacon
          | build_dec (TyvarVariance _) = Path.TyvarVariance
          | build_dec (DatatypeWith _) = Path.DatatypeWith
          | build_dec (TestSubtype _) = Path.TestSubtype
    in
        build exp
    end

    fun isVal e =
        case e of
            Const _ => true
          | Var _ => true
          | Con _ => true
          | Case _ => false
          | Fn _ => true
          | App _ => false
          | Conapp (_, (loc, e0)) => isVal e0
          | RecordExp (_, (loc, e0)) => isVal e0
          | Merge exps => List.all (fn (loc,e) => isVal e) exps
          | Tuple exps => List.all (fn (loc,e) => isVal e) exps
          | Proj _ => false
          | Let _ => false
          | Lethint _ => false
          | Anno ((loc, e0), _) => isVal e0
          | LET(_, (loc1, e1), e2) => (isVal e1) andalso (isVal e2)
(*          | LETDN _ => false *)
          | LETSLACK(_, (loc1, e1), e2) => (isVal e1) andalso (isVal e2)
          | Lvar _ => true
          | Raise _ => false
          | Handle _ => false
          | Spy(_, (loc, e0)) => isVal e0
          | Leftanno(_, (loc, e0)) => isVal e0

    fun isSynth e =
        case e of
            Const _ => true
          | Var _ => true
          | Con _ => true
          | Case _ => false
          | Fn _ => false
          | App _ => true
          | Conapp (_, (loc, e0)) => false
          | RecordExp (_, (loc, e0)) => false
          | Merge exps => false
          | Tuple exps => false
          | Proj _ => true
          | Let _ => false
          | Lethint _ => false
          | Anno ((loc, e0), _) => true
          | LET(_, (loc1, e1), e2) => false
(*          | LETDN _ => false *)
          | LETSLACK(_, (loc1, e1), e2) => false
          | Lvar _ => true
          | Raise _ => false
          | Handle _ => false
          | Spy(_, (loc, e0)) => isSynth e0
          | Leftanno(_, (loc, e0)) => isSynth e0

   fun patternToString p = case p of
             VarPattern x => PV.toString x
           | WildPattern => "_"
           | CtorPattern (c, NONE) => PV.toString c
           | CtorPattern (c, SOME p0) => PV.toString c ^ " " ^ patternToString p0
           | RecordPattern (fld, p) => "{" ^ fld ^ " = " ^ patternToString p ^ "}"

           | TuplePattern [] => "()"
           | TuplePattern ps => "(" ^ Separate.list ", " (List.map patternToString ps) ^ ")"

           | OrPattern [] => "(_empty_)"
           | OrPattern ps =>  "(" ^ Separate.list " | " (List.map patternToString ps) ^ ")"

           | AsPattern (x, p0) => "(" ^ PV.toString x ^ " as " ^ patternToString p0 ^ ")"
           | StringPattern (s) => "\"" ^ String.toString s ^ "\""
           | IntPattern (i) => Int.toString i

   fun patternOptionToString p = case p of
             NONE => "---"
           | SOME p => patternToString p

   fun quantifyCtype texp tvinfos = case tvinfos of
           [] => texp
         | (Tvinfo(tv,_) :: rest) =>
               let val tv' = TV.new tv
               in
                   All(tv', Types.outer_universe, substTypevar [(tv, Typevar tv')] (quantifyCtype texp rest))
               end

  fun mkSect (Top, A2) = A2
    | mkSect (A1, Top) = A1
    | mkSect (A1, A2) = Sect(A1, A2)

(*
   fun quantifiedConstructor tvinfos (Constructor{c, basetype, contype}) =
       let val 
       Constructor{c= c,
                   basetype= quantifyCtype basetype tvinfos, 
                   contype= quantifyCtype contype tvinfos}
*)
end
