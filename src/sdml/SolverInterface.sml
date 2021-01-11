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
signature SOLVER_INTERFACE = sig
    type context
    
    val getLocation : unit -> Stardustrc.program_location option
    
    datatype assertresult =
        Unsat
      | Ok of context * (Indexing.exp * Indexing.exp) list
      | Valid

    structure Context : sig
        val new : Stardustrc.program_location option (* NONE for shared libraries, whose finding and loading is handled
                                                        by *-ffi/*-h.sml anyway *)
               -> context option
        val fromSession : Piper.session -> context
    end
    
    val assert : context * Indexing.constraint * (IndexSym.sym -> Indexing.exp)
                 -> assertresult * Indexing.constraint list (* disjuncts *)
    val isValidEq : (Indexing.constraint -> bool)
        -> context * Indexing.sort * (Indexing.exp * Indexing.exp)
        -> bool
    val isValidPred : context * (IndexSym.sym * Indexing.exp) -> bool
    val rollback : ((*present -- IGNORED by Cvc4Piped*)context * (*old context to roll back to*)context) -> context

    val getEqs : context -> (IndexSym.sym -> Indexing.exp)
        -> (Indexing.exp * Indexing.exp) list

    val declare : context * (IndexSym.sym * Indexing.sort) -> assertresult
    val save : context -> (context * (context(*IGNORED by Cvc4Piped*) -> context))

    val knowsSym : context -> IndexSym.sym -> bool

    val negate : Indexing.constraint -> Indexing.constraint

    val resultize : context -> assertresult -> (context -> 'a) -> (context -> 'a) -> 'a
    
    val glork : context -> string

    type point = int
    val push : context -> context * point
    val popto : context * point -> context

    val reset : unit -> unit (* Resets local state, *not* constraint solver! *)

    val canHandleBooleans : bool
end (* signature SOLVER_INTERFACE *)
