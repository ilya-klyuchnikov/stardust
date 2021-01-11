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
signature LOCATION = sig
  type location 
  type locations
  
  val fromPositions : int * int * int * int -> location
 
  val toString : location -> string
  (* val toUnderlinedExcerpt : string(*pathname*) -> location -> string *)

  val toPositions : location -> int * int * int * int

  val span : location -> location -> location

  val nullLocations : locations
  val singleton : location -> locations
  val addLocation : locations ->  location -> locations
  val bogus : location
end (* signature LOCATION *)



structure Location :> LOCATION = struct
  type location = (int * int) * (int * int)   (* start line, column; end line, column;  all 1-based *)
  type locations = location list

  fun fromPositions (startline, startcol, endline, endcol) = ((startline, startcol), (endline, endcol))

  fun toPositions ((startline, startcol), (endline, endcol)) = (startline, startcol, endline, endcol)

  fun span ((startline1, startcol1), (endline1, endcol1))
                   ((startline2, startcol2), (endline2, endcol2)) = ((startline1, startcol1), (endline2, endcol2))

  val bogus = fromPositions (0,0, 0,0)

  fun toString ((startline, startcol), (endline, endcol)) =
      let val sline = Int.toString startline
          and scol = Int.toString startcol
          and eline = Int.toString endline
          and ecol = Int.toString endcol
      in
          if (startline = endline) andalso (startcol = endcol) then
              "line " ^ sline ^ " " ^ "col " ^ scol
          else if startline = endline then
              "line " ^ sline ^ " " ^ "col " ^ scol ^ "-" ^ ecol
          else  (* location on multiple lines, so don't display column *)
              "lines " ^ sline ^ "-" ^ eline
      end


  val nullLocations = []

  fun singleton loc = [loc]

  fun addLocation locs loc = locs @ [loc]

end (* structure Location *)
