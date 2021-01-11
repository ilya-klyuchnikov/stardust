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
signature EQ = sig
  type t
  val eq : t * t -> bool
end

signature PR = sig
  type t
  val toString : t -> string
end

(* Rule 77 of the Definition can bite me.
   Corollary: MLton can bite me. *)
(*
signature EQ_PR = sig
  include EQ
  include PR
end

signature EQ_PR_TEX = sig
  include EQ
  include PR_TEX
end
*)

signature EQ_PR = sig
  include EQ
  val toString : t -> string
end
