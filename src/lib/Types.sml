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
signature TYPES = sig

    datatype universe = Typelevel of int

    datatype texp =
        Typevar of TV.sym
      | Extypevar of TV.sym
      | All of TV.sym * universe * texp
      
      | Arrow of texp * texp
      | Product of texp list
      | Tycon of TC.sym * Indexing.record * texp list
      
      | Record of string * texp
      
      | Top
      | Bot      
      | Sect of texp * texp
      | Union of texp * texp
      
   (* refinement types *)
      | Rsect of texp * texp
      | Runion of texp * texp
      | Univ of IndexSym.sym * Indexing.sort * texp
      | Exis of IndexSym.sym * Indexing.sort * texp
      | Implies of Indexing.constraint * texp
      | Conj of Indexing.constraint * texp

    structure Variance : sig
        datatype t =
          Non | Co | Contra

        val toString : t -> string   (* "Non" | "Co" | "Contra" *)
        val toDeclString : t -> string  (* "", "+", "-" *)
    end

    datatype tvinfo = Tvinfo of TV.sym * Variance.t

    val outer_universe : universe
    val inner_universe : universe -> universe
    val contains : universe -> universe -> bool
    val lesser : universe * universe -> universe
    val toString : universe -> string
    val toString' : universe -> string     (* Returns "" if outer_universe *)

    val least_universe : texp -> universe
    val shift_universe : texp -> texp

    val ground : texp -> bool

    val substIndex : (Indexing.sym * Indexing.exp) list -> texp -> texp

    datatype flavor = SubstTypevarUniversal | SubstTypevarExistential

    val substTypevar : (TV.sym * texp) list -> texp -> texp
    val substExtypevar : (TV.sym * texp) list -> texp -> texp
    val substTypevarAux : flavor -> (TV.sym * texp) list -> texp -> texp
 
    val typeToString : texp -> string

    datatype typedec = 
        Datatype of {tc : TC.sym,
                     builtin : bool,   (* built-in in target language? *)
                     params : tvinfo list,
                     sorting : Indexing.Sorting.t,
                     constructors : con list}
      | Synonym of {tc : TC.sym,
                    tv : TV.sym,
                    params : TV.sym list,
                    definition : texp}
    
    and con = Constructor of {c: PV.sym,
                              nullary: bool,
                              basetype: texp,
                              conjuncts: (PV.sym * texp) list,
                              elaborated_conjuncts: (PV.sym * texp) list,
                              contype: texp}
    
    type typedecs = typedec list
end



structure Types :> TYPES = 
struct
    
    structure Variance = struct
        datatype t =
          Non | Co | Contra

        fun toString v = case v of
              Non => "Non"
            | Co => "Co"
            | Contra => "Contra"

        fun toDeclString v = case v of
              Non => ""
            | Co => "+"
            | Contra => "-"
    end
    
    datatype tvinfo = Tvinfo of TV.sym * Variance.t

    datatype universe = Typelevel of int
    
(*  val outer_universe : universe *)
    val outer_universe = Typelevel 0

(*  val inner_universe : universe -> universe *)
    fun inner_universe (Typelevel n) = Typelevel (n + 1)

(*  val contains : universe -> universe -> bool *)
    fun contains (Typelevel m) (Typelevel n) =
      m < n

(*  val lesser : universe * universe -> universe *)
    fun lesser (u1, u2) =
      if contains u1 u2 then u2
      else u1

(* val toString : universe -> string *)
    fun toString (Typelevel n) = "@" ^ Int.toString n

(* val toString' : universe -> string     (* Returns "" if outer_universe *) *)
    fun toString' (u as Typelevel n) =
        if n = 0 then ""
        else toString u

    datatype texp =
        Typevar of TV.sym
      | Extypevar of TV.sym
      | All of TV.sym * universe * texp
      
      | Arrow of texp * texp
      | Product of texp list
      | Tycon of TC.sym * Indexing.record * texp list
      
      | Record of string * texp
      
      | Top
      | Bot      
      | Sect of texp * texp
      | Union of texp * texp
      
   (* refinement types *)
      | Rsect of texp * texp
      | Runion of texp * texp
      | Univ of IndexSym.sym * Indexing.sort * texp
      | Exis of IndexSym.sym * Indexing.sort * texp
      | Implies of Indexing.constraint * texp
      | Conj of Indexing.constraint * texp


(* val least_universe : texp -> universe *)
    fun least_universe A =
      let val f = least_universe
          val m = outer_universe
          fun lesser_list [] = m
            | lesser_list (x::xs) = lesser(f x, lesser_list xs)
      in case A of
        Typevar _ => m
      | Extypevar _ => m
      | All (_, u, A0) => lesser(u, f A0)
      | Arrow (A1, A2) => lesser(f A1, f A2)
      | Product As => lesser_list As
      | Tycon (_, _, As) => lesser_list As
      | Sect (A1, A2) => lesser(f A1, f A2)
      | Union (A1, A2) => lesser(f A1, f A2)
      | Rsect (A1, A2) => lesser(f A1, f A2)
      | Runion (A1, A2) => lesser(f A1, f A2)
      | Univ (_, _, A0) => f A0
      | Exis (_, _, A0) => f A0
      | Top => m
      | Bot => m
      | Record (_, A0) => f A0
      | Implies (_, A0) => f A0
      | Conj (_, A0) => f A0
     end

(* val ground : texp -> bool *)
    fun ground A =
      let in case A of
        Typevar _ => true
      | Extypevar _ => true
      | All(_, u, A0) => false
      | Arrow(A1, A2) => ground A1 andalso ground A2
      | Product As => List.all ground As
      | Tycon (_, _, As) => List.all ground As
      | Sect (A1, A2) => ground A1 andalso ground A2
      | Union (A1, A2) => ground A1 andalso ground A2
      | Rsect (A1, A2) => ground A1 andalso ground A2
      | Runion (A1, A2) => ground A1 andalso ground A2
      | Univ(_, _, A0) => ground A0
      | Exis(_, _, A0) => ground A0
      | Top => true
      | Bot => true
      | Record(_, A0) => ground A0
      | Implies(_, A0) => ground A0
      | Conj(_, A0) => ground A0
     end


(* val shift_universe : texp -> texp *)
    fun shift_universe A =
      let val self = shift_universe
      in case A of
           Typevar tv => Typevar tv
         | Extypevar tv => Extypevar tv
         | All(tv, uu, A) => All(tv, inner_universe uu, self A)
         | Arrow(d, cod) => Arrow(self d, self cod)
         | Product texps => Product (map (self) texps)
         | Tycon (tc, index, texps) =>Tycon(tc, index, map self texps) 
         | Sect(A, B) => Sect(self A, self B)
         | Union(A, B) => Union(self A, self B)
         | Rsect(A, B) => Rsect(self A, self B)
         | Runion(A, B) => Runion(self A, self B)
         | Univ(a, sort, texp) => Univ(a, sort, self texp)
         | Exis(a, sort, texp) => Exis(a, sort, self texp)
         | Top => Top
         | Bot => Bot
         | Record(fld, A) => Record(fld, self A)
         | Implies(P, A) => Implies(P, self A)
         | Conj(P, A) => Conj(P, self A)        
     end

(*
    datatype tscm =
        Tscm of TV.sym list * texp
*)
    datatype flavor = SubstTypevarUniversal | SubstTypevarExistential

    (* WARNING:
     
     substIndex assumes that the index expressions substituting for index variables
       contain no index variables bound by quantifiers in texp.
     This is NOT capture-avoiding substitution!
   *)
    fun substIndex assoc texp =
        let val self = substIndex assoc
        in
            case texp of
               Typevar tv => Typevar tv
             | Extypevar tv => Extypevar tv
             | All(tv, uu, A) => All(tv, uu, self A)
             | Arrow(d, cod) => Arrow(self d, self cod)
             | Product texps => Product (map (self) texps)
             | Tycon (tc, record, texps) =>Tycon(tc, Indexing.subst_record assoc record, map self texps) 
             | Sect(A, B) => Sect(self A, self B)
             | Union(A, B) => Union(self A, self B)
             | Rsect(A, B) => Rsect(self A, self B)
             | Runion(A, B) => Runion(self A, self B)
             | Univ(a, sort, texp) => Univ(a, sort, self texp)
             | Exis(a, sort, texp) => Exis(a, sort, self texp)
             | Top => Top
             | Bot => Bot
             | Record(fld, A) => Record(fld, self A)
             | Implies(P, A) => Implies(Indexing.Constraint.subst assoc P, self A)
             | Conj(P, A) => Conj(Indexing.Constraint.subst assoc P, self A)
        end

    (* WARNING: not capture-avoiding
   *)
    fun substTypevarAux flavor assoc texp =
     let val self = substTypevarAux flavor assoc
     in
        case texp of
            Typevar tv =>
              let in case Assoc.getOpt assoc tv of
                         SOME replacement =>
                            let in case flavor of SubstTypevarUniversal => replacement
                                                | SubstTypevarExistential => (print ("substTypevarAux: replacing existential, but found Typevar?!\n"); Typevar tv)
                            end
                       | NONE => Typevar tv
              end
      | Extypevar tv =>
              let in case Assoc.getOpt assoc tv of
                         SOME replacement =>
                            let in case flavor of SubstTypevarExistential => replacement
                                                | SubstTypevarUniversal => (print ("substTypevarAux: replacing universal, but found Extypevar?!\n"); Extypevar tv)
                            end
                       | NONE => Extypevar tv
              end
      | All(tv, uu, texp) => All(tv, uu, self texp)
      | Tycon (tc, index, texps) => Tycon(tc, index, map self texps)
      
      | Arrow(d, cod) => Arrow(self d, self cod)
      | Product texps => Product (map (self) texps)
      | Sect(A, B) => Sect(self A, self B)
      | Union(A, B) => Union(self A, self B)
      | Rsect(A, B) => Rsect(self A, self B)
      | Runion(A, B) => Runion(self A, self B)
      | Univ(a, sort, texp) => Univ(a, sort, self texp)
      | Exis(a, sort, texp) => Exis(a, sort, self texp)
      | Top => Top
      | Bot => Bot
      | Record(fld, A) => Record(fld, self A)
      | Implies(P, A) => Implies(P, self A)
      | Conj(P, A) => Conj(P, self A)
     end

    fun substTypevar assoc texp = substTypevarAux SubstTypevarUniversal assoc texp
    fun substExtypevar assoc texp = substTypevarAux SubstTypevarExistential assoc texp

    fun typeToString texp =
          let
              val self = typeToString
          in
                case texp of
                    Typevar tv => "(Typevar " ^ TV.toString tv ^ ")"
                  | Extypevar tv => "(Extypevar " ^ TV.toString tv ^ ")"
                  | All(tv, uu, texp) => "(All "  ^ TV.toString tv ^ " " ^ "_" ^ " " ^ self texp ^ ")"
                  | Tycon (tc, index, texps) => "(Tycon " ^ TC.toString tc ^ " " ^ "index" ^ " " ^ " " ^ Separate.list " " (List.map self texps) ^ ")"

                  | Arrow(d, cod) => "(Arrow " ^ self d ^ " " ^ self cod ^ ")"
                  | Product texps => "(Product " ^ Separate.list " " (List.map self texps) ^ ")"
                  | Sect(A, B) => "(Sect " ^ self A ^ " " ^ self B ^ ")"
                  | Union(A, B) =>  "(Union " ^ self A ^ " " ^ self B ^ ")"
                  | Rsect(A, B) => "(Rsect " ^ self A ^ " " ^ self B ^ ")"
                  | Runion(A, B) =>  "(Runion " ^ self A ^ " " ^ self B ^ ")"
                  | Univ(a, sort, texp) => "(Univ(a, sort, " ^ self texp ^ ")"
                  | Exis(a, sort, texp) =>  "(Exis(a, sort, " ^ self texp ^ ")"
                  | Top => "Top"
                  | Bot => "Bot"
                  | Record(fld, A) => "Record(" ^ fld ^ " " ^ self A ^ ")"
                  | Implies(P, A) => "Implies(P, " ^ self A ^ ")"
                  | Conj(P, A) => "Conj(P, " ^ self A ^ ")"
          end


    datatype typedec = 
        Datatype of {tc : TC.sym,
                     builtin : bool,   (* built-in in target language? *)
                     params : tvinfo list,
                     sorting : Indexing.Sorting.t,
                     constructors : con list}
      | Synonym of {tc : TC.sym,
                    tv : TV.sym,
                    params : TV.sym list,
                    definition : texp}
    
    and con = Constructor of {c: PV.sym,
                              nullary: bool,
                              basetype: texp,
                              conjuncts: (PV.sym * texp) list,
                              elaborated_conjuncts: (PV.sym * texp) list,
                              contype: texp}
  
    type typedecs = typedec list
    
end
