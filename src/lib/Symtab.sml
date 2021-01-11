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
signature SYMTAB = sig
  eqtype sym
  
  val reset : unit -> unit
  
  val proper_name : sym -> string
  
  val new : sym -> sym
  val toString : sym -> string
  val toShortString : sym -> string
  val fresh : string -> sym
  val sanitary_fresh : string -> string -> sym
  
  val isNonsense : sym -> bool   (* true iff integer value is negative *)
  val toInt : sym -> int
  val fromInt : int -> sym
  
end (* signature SYMTAB *)




functor SymtabFn (structure A :  sig
                                   val table_name : string  (* e.g. "PV" *)
                                   val prefix : string
                               end) :> SYMTAB
=
struct
  type sym = int

  type entry' = string * string option
  type entry = entry' option
  
  fun toInt sym = sym
  fun fromInt sym = sym

  fun isNonsense sym = (toInt sym < 0)

  val table : entry DynamicArray.array = DynamicArray.array (16, NONE)
  val var_count : int ref = ref 0
  
  fun next () = !var_count before var_count := (!var_count) + 1

  fun reset () =
      ((*print ("Symtab `" ^ A.table_name ^ "' reset"); *)
       DynamicArray.truncate (table, 0);
       var_count := 0)

  fun name n = 
      if n = ~1 then SOME ("_", SOME "_")
      else
          let in 
              DynamicArray.sub (table, n)
          end
          handle Subscript => NONE

  fun proper_name n = 
      case name n of
          NONE => raise Option
        | SOME (s, _) => s

  fun fresh name = 
      let val n = next() 
      in 
          DynamicArray.update (table, n, SOME (name, NONE));
          n
      end

  fun sanitary_fresh name sanitary_name = 
      let val n = next() 
      in 
          DynamicArray.update (table, n, SOME (name, SOME sanitary_name));
          n
      end

  fun new v =
      let val nm = case name v of
                     SOME (s, _) => s
                   | NONE => Int.toString v
      in
          fresh nm
      end

  fun toString sym = 
      case name sym of
        SOME (_, SOME s2) => s2
      | SOME (s1, NONE) =>
            A.prefix ^ (Int.toString sym) ^ "_" ^ s1
      | NONE => A.prefix ^ (Int.toString sym) ^ "!!!"

  fun toShortString sym = 
      case name sym of
          SOME (s1, NONE) => s1
      | _ => toString sym

end (* functor SymtabFn *)



(* Program Variables *)
structure PV' = SymtabFn (structure A = struct
                                           val table_name = "PV"
                                           val prefix = "x"
                                       end)

structure PVExtra = struct
   structure PVCore = PV'
   val underscore = PVCore.fromInt (~1)

   val inl_magic = ~111
   val inr_magic = ~222
   val inl = PVCore.fromInt inl_magic
   val inr = PVCore.fromInt inr_magic

   fun toML pv =
       let val n = PVCore.toInt pv
       in
           if n = inl_magic then
               "Inl"
           else if n = inr_magic then
               "Inr"
           else
               PVCore.toString pv
       end
end
structure PV = PVExtra.PVCore


structure PVStatistEnv = EnvFn (structure E = IntStatistEnv)
structure PVEnv = EnvFn (structure E = IntEnv)



(* Type Variables *)
structure TV = SymtabFn (structure A = struct
                                           val table_name = "TV"
                                           val prefix = "'tv"
                                       end)
structure TVStatistEnv = EnvFn (structure E = IntStatistEnv)
structure TVEnv = EnvFn (structure E = IntEnv)


(* Type Constructors *)
structure TC' = SymtabFn (structure A = struct
                                           val table_name = "TC"
                                           val prefix = "tc"
                                       end)
structure TCStatistEnv = EnvFn (structure E = IntStatistEnv)
structure TCEnv = EnvFn (structure E = IntEnv)

structure TCExtra = struct
   structure TCCore = TC'

   val sum_magic = ~4
   val sum = TCCore.fromInt sum_magic

   fun toML pv =
       let val n = TCCore.toInt pv
       in
           if n = sum_magic then
               "sum"
           else
               TCCore.toShortString pv
       end
end
structure TC = TCExtra.TCCore



(* Index Symbols: variables, functions, predicates *)
structure IndexSym = SymtabFn (structure A = struct
                                           val table_name = "IndexSym"
                                           val prefix = "iv"
                                       end)
structure IndexSymStatistEnv = EnvFn (structure E = IntStatistEnv)
structure IndexSymEnv = EnvFn (structure E = IntEnv)



(* Index Sorts *)
structure IndexSortSym = SymtabFn (structure A = struct
                                           val table_name = "IndexSortSym"
                                           val prefix = ""
                                       end)
structure IndexSortSymStatistEnv = EnvFn (structure E = IntStatistEnv)
structure IndexSortSymEnv = EnvFn (structure E = IntEnv)



(* Index Field Names *)
structure IndexFieldName = SymtabFn (structure A = struct
                                           val table_name = "IndexFieldName"
                                           val prefix = ""
                                       end)
structure IndexFieldNameStatistEnv = EnvFn (structure E = IntStatistEnv)
structure IndexFieldNameEnv = EnvFn (structure E = IntEnv)
