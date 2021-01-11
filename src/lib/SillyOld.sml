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

  val Array_foldli = Array.foldli
  val Array_appi = Array.appi
  fun newArray_appi f arr = Array.appi f (arr, 0, NONE)
  val Array_modifyi = Array.modifyi
  fun newArray_modifyi f arr = Array.modifyi f (arr, 0, NONE)

  val TextIO_inputLine = TextIO.inputLine
  val Timer_checkCPUTimer = Timer.checkCPUTimer

  structure Option = struct
    exception Option 
    val getOpt = Option.getOpt
    val isSome = Option.isSome
    val valOf = Option.valOf
    val filter = Option.filter
    val join = Option.join
    val map = Option.map
    val mapPartial = Option.mapPartial
    val compose = Option.compose
    val composePartial = Option.composePartial
    fun app f x =
	let val _ = Option.map f x
	in
	    ()
	end
  end

  structure String = struct
      type string = String.string
      fun isSuffix s1 s2 =
          let val size1 = size s1
              val size2 = size s2
          in
              (size1 <= size2)
              andalso
                let val s1 = Substring.all s1
                    val s2 = Substring.slice (Substring.all s2, size2 - size1, SOME size1)
                in
                    case Substring.compare (s1, s2) of
                        EQUAL => true
                      | _ => false
                end
	  end
      fun isSubstring s1 s2s =
	  (String.isPrefix s1 s2s)
	  orelse
	    let val s2 = Substring.all s2s
		val (p1, p2) = Substring.position s1 s2
		val _ = print ("p1 = `" ^ Substring.string p1 ^ "'; p2 = `" ^ Substring.string p2 ^ "'\n")
	    in
		Substring.size p1 < size s2s
	    end
  val maxSize = String.maxSize
  val size = String.size
  val sub = String.sub
  val substring = String.substring
  val extract = String.extract
  val concat = String.concat
  val op^ = String.^
  val str = String.str
  val implode = String.implode
  val explode = String.explode
  val fromString = String.fromString
  val toString = String.toString
  val fromCString = String.fromCString
  val toCString = String.toCString
  val map = String.map
  val translate = String.translate
  val tokens = String.tokens
  val fields = String.fields
  val isPrefix = String.isPrefix
  val compare = String.compare
  val collate = String.collate
  val op<= = String.<=
  val op< = String.<
  val op>= = String.>=
  val op> = String.>
  end (* structure String *)
end

structure Word8VectorSlice = struct
  val full = fn x => {buf= x, i= 0, sz= NONE}
end
