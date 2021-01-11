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
signature ENV = sig
  eqtype sym
  type 'a env

  val empty : unit -> 'a env
  val extend : 'a env -> (sym * 'a) list -> 'a env
  val get : 'a env -> sym -> 'a option

  val toList : 'a env -> (sym * 'a) list
end


(* Define an identity functor.  Since SML functors are generative, this guarantees
  
    - fresh state for stateful environments (i.e. IntStatistEnv), and
    - distinguished sym types (all environments).
*)
functor EnvFn
   (structure E : ENV)
    :>
    ENV
=
struct

  open E

end (* functor EnvFn *)


structure IntStatistEnv : ENV = struct
  
  type sym = int
  type 'a env = 'a option DynamicArray.array
  
  fun empty () = DynamicArray.array (16, NONE)
  
  fun extend e list = case list of
      [] => e
    | ((k, v) :: list) =>
           let in
               DynamicArray.update (e, k, SOME v);
               extend e list
           end
  
  fun get e n =
      DynamicArray.sub (e, n)
  
  fun toList e =
      DynamicArray.foldli (fn (i, entry, list) =>
                              case entry of
                                  SOME v => (i, v) :: list
                                | NONE => list)
                          []
                          e

end (* structure IntStatistEnv *)



functor BinaryMapEnv
   (structure K : sig
                    eqtype ord_key
                    val equal : ord_key * ord_key -> bool
                    val compare : ord_key * ord_key -> order
    end)
   :
   ENV
=
struct
  structure Map = BinaryMapFn (K)
  
  type sym = K.ord_key
  type 'a env = 'a Map.map
  
  fun empty () = Map.empty
  
  fun extend e list = case list of
        [] => e
    | ((k, v) :: rest) => extend (Map.insert (e, k, v)) rest
  
  fun get e i =
      Map.find (e, i)
  
  fun toList e =
      Map.listItemsi e

end  (* functor BinaryMapEnv *)


structure IntEnv : ENV =
                         BinaryMapEnv (structure K = struct
                                           type ord_key = int 
                                           fun equal (x : int, y) = (x = y)
                                           val compare = Int.compare
                                       end)

structure StringEnv : ENV =
                         BinaryMapEnv (structure K = struct
                                           type ord_key = string 
                                           fun equal (x : string, y) = (x = y)
                                           val compare = String.compare
                                       end)
