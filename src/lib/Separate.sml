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
signature SEPARATE = sig

    val list : string -> string list -> string

    val unseparate : char -> string -> string list

end (* signature SEPARATE *)


structure Separate :> SEPARATE = struct

  fun list separator xs = case xs of
      [] => ""
    | [x] => x
    | x :: xs => x ^ separator ^ list separator xs

  fun unseparate separator s =
    String.tokens (fn ch => ch = separator) s
  
  val colon = list ":"
  val comma = list ","
  val newline = list "\n"
  val semi = list ";"
  val space = list " "

end (* structure Separate *)
