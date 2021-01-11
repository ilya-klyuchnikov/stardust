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
(* simple-uref.sml
 *
 * UNIONFIND DATA STRUCTURE WITH PATH COMPRESSION
 *
 * Author:
 *    Fritz Henglein
 *    DIKU, University of Copenhagen
 *    henglein@diku.dk
 *)

structure SimpleURef : UREF =
  struct

    exception UnionFind of string

    datatype 'a urefC
      = ECR of 'a
      | PTR of 'a uref
    withtype 'a uref = 'a urefC ref

    fun find (p as ref(ECR _)) = p
      | find (p as ref(PTR p')) = let
	  val p'' = find p'
          in
	    p := PTR p''; p''
          end

    fun uRef x = ref (ECR x)

    fun !! p = (case !(find p)
	   of ECR x => x
	    | _ => raise Match
	  (* end case *))
      
    fun equal (p, p') = (find p = find p')

    fun update (p, x) = let val p' = find p
	  in
	    p' := ECR x
	  end

    fun link (p, q) = let
	  val p' = find p
          val q' = find q
	  in
	    if p' = q' then false else (p' := PTR q'; true)
	  end
 
    val union = link

    fun unify f (p, q) = let
	  val v = f(!!p, !!q)
	  in
	    union (p, q) before update (q, v)
	  end

  end (* SimpleURef *)

