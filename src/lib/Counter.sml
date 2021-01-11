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
signature COUNTER = sig

    val INC : string -> int ref -> unit

end


structure Counter :> COUNTER = struct

  fun INC s x = (x := (!x) + 1;
                 if (!x) mod 2048 = 0 then
                     print (s ^ " := " ^ Int.toString (!x) ^ "\n")
                 else ())

end (* structure Counter *)
