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
(* File: Renaming.sml
 * Author: Joshua Dunfield
 * Contents: Renamings---maps from variables to variables,
 *   used in connection with memoization in Typecheck.sml.
 *)

signature RENAMING = sig

  type var = IndexSym.sym
  type varmap

  val empty : varmap
  val compose : varmap -> varmap -> varmap
  val apply : varmap -> var -> var
  val inverse : varmap -> varmap

  val extend : var * var -> varmap -> varmap

  val toList : varmap -> (var * var) list
  val fromList : (var * var) list -> varmap

  val toString : varmap -> string
end (* signature RENAMING *)


structure Renaming :> RENAMING = struct

  
  type var = IndexSym.sym
  type varmap = (var * var) list

  val empty = []

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

  fun compose m1 m2 =
      MyList.elimDups (comp m1 m2)

  fun apply s a =
      case Assoc.getOpt s a of
          NONE => a
        | SOME a' => a'

  fun elemToString (sym1, sym2) =
      "(" ^ IndexSym.toString sym1 ^ " |-> " ^ IndexSym.toString sym2 ^ ")"
  
  fun inverse s =
      map (fn (a, b) => (b, a)) s
  
  fun toString varmap =
      Separate.list ", " (map elemToString varmap)

  fun extend (a, b) s =
      (a, b) :: s

  fun toList varmap =
      varmap

  fun fromList list =
      list

end (* structure Renaming *)
