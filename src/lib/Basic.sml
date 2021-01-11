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
signature BASIC = sig
    
    val cross : ('a -> 'aa) -> ('b -> 'bb) -> ('a * 'b) -> ('aa * 'bb)
    
    (* option *)
    val optionPair : 'a option * 'b option -> ('a * 'b) option

    val mapapply : ('a -> 'b) list -> 'a -> 'b list  (* mapapply [f1, ..., fn] x = [f1 x, ..., fn x] *)

end (* signature BASIC *)



structure Basic :> BASIC = struct

  fun cross f g (x, y) = (f x, g y)

  fun optionPair (NONE, NONE) = NONE
    | optionPair (SOME a, SOME b) = SOME (a, b)
    | optionPair _ = raise Option

  fun mapapply fs x = case fs of
       [] => []
     | f::fs => (f x) :: (mapapply fs x)

end (* structure Basic *)
