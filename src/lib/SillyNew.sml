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
structure Silly = struct

   fun Array_foldli f b (array, int, int_option) =
       Array.foldli f b array

   fun Array_appi f (array, int, int_option) =
       Array.appi f array

   fun Array_modifyi f (array, int, int_option) =
       Array.modifyi f array

   val newArray_appi = Array.appi
   val newArray_modifyi = Array.modifyi

   fun TextIO_inputLine ic =
       case TextIO.inputLine ic of
           NONE => ""
         | SOME stuff => stuff
 
   fun Timer_checkCPUTimer t =
       let val r = Timer.checkCPUTimer t
       in
           {gc= Time.fromSeconds 0, sys= #sys(r), usr= #usr(r)}
       end
  
   structure String = String
end
