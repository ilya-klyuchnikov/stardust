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
signature ASSOC = sig

    (* Associative lists *)

    val get : (''a * 'b) list -> ''a -> 'b
    val getOpt : (''a * 'b) list -> ''a -> 'b option

    val domain : ('a * 'b) list -> 'a list
    val eq : ('a * 'a -> bool) -> ('a * 'b) list -> 'a -> 'b option

    val apply : (''a * ''a) list -> ''a -> ''a

end


structure Assoc :> ASSOC = struct

  fun get assoc k =
      #2 (Option.valOf (List.find (fn (k', _) => k = k') assoc))

  fun domain (assoc : ('a * 'b) list) =
      List.map #1 assoc
  
  fun eq f (assoc : ('a * 'b) list) k =
      case List.find (fn (k', v) => f (k, k')) assoc of
          NONE => NONE
        | SOME (_, v) => SOME v

  fun getOpt assoc k = eq (op=) assoc k



  fun apply assoc k =
      case List.find (fn (k', k'') => k=k') assoc of
          NONE => k
        | SOME (_, k'') => k''

end (* structure Assoc *)
