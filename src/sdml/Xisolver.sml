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
(* Straight port of Hongwei Xi's dsolver.ml *)

(* 
 * A direct implementation of Fourier-Motzkin's approach to solving linear inequalities *)
(* use fixed length of vectors to represent linear inequalities:
 * for instance: 3x + 4y - 5 >= 0 is represented as
 * -5 3 4
 *)

signature XISOLVER = sig
  exception Contradiction
  exception Tautology
  type store

  val mk_store : int list list -> store
  val store_solve : int -> store -> unit   (* Can raise Contradiction or Tautology *)
end

structure Xisolver :> XISOLVER = struct

  open Silly

  exception Contradiction
  exception Tautology

  type store = int array list

  fun mk_store lists =
      List.map Array.fromList lists

  val number_of_variables = ref 0

  fun $ (a, n) = Array.sub(a, n)
  infix $

  fun output_leq leq =
      (print (Int.toString (leq $ 0));
       print " >= "; 
       Array.app (fn x => print (Int.toString x ^ " ")) leq;
       print "; ")

  fun show_leq msg leq = 
      (print msg; output_leq leq; print "\n")


  fun  show_store msg store =
      (print msg;
       List.app (fn leq => (output_leq leq; print "\n")) store)

  fun leq_first leq = (* yields the first nonzero coefficient *)
    let fun aux i n =
       if i > n then
           if (leq $ 0) < 0 then
               raise Contradiction
           else
               raise Tautology
       else if (leq $ i) <> 0 then
           i
       else aux (i+1) n
    in
        aux 1 (!number_of_variables)
    end
  
  exception Leq_least
  
  fun leq_least store =
    let fun aux1 nz i arg = case arg of
        [] => nz
      | leq :: rest =>
             if ~1 <= (leq $ i) andalso (leq $ i) <= 1 then
                 (if nz then
                      aux1 nz i rest
                  else
                      aux1 ((leq $ i) <> 0) i rest)
            else
                false

        fun aux2 i =
            if i > (!number_of_variables) then
                let in
                     show_store "leq_least: store is \n" store;
                     leq_first (List.hd store)
                end
            else if aux1 false i store then
                i
            else aux2 (i+1)
    in
        aux2 1
    end


  fun leq_aff_add m leq n leq' =
    let val ans = Array.array ((!number_of_variables) + 1, 0)
    in
        Array_modifyi (fn (i, _) => m * (leq $ i) + n * (leq' $ i)) (ans, 0, NONE);
(*        for i = 0 to !number_of_variables do
          ans $ (i) <-  m * leq.(i) + n * leq'.(i)
        done; *)
        ans
    end

  fun gcd m n =
      if m = 0 then
          n
      else
          if n = 0 then
              m
          else
              gcd n (m mod n)

  fun leq_norm leq =
    let val n = ref 0
    in
      Array_appi (fn (i, x) => n := gcd (!n) (abs x)) (leq, 1, SOME (!number_of_variables));
  (*
      show_leq ("leq_norm: " ^ (Int.toString !n) ^ "\n") leq;
  *)
      let val n = !n
      in
          if n > 1 then
                 (Array_modifyi (fn (i, x) => x div n) (leq, 1, SOME (!number_of_variables));
(*                  for i = 1 to !number_of_variables do leq.(i) <- leq.(i) div n done; *)
                  let val new_zeroth = 
                      if (leq $ 0) >= 0 then (leq $ 0) div n
                      else (((  if (leq $ 0) mod n = 0 then (leq $ 0) div n
                                else (leq $ 0) div n - 1  )))
                  in
                      Array.update (leq, 0, new_zeroth)
                  end)
          else
              ()
      end
    end

  fun leq_combine i neg pos store =
    let val leq = leq_aff_add (pos $ i) neg (~ (neg $ i)) pos
    in
        let val _ = leq_first leq
            val _ = leq_norm leq
        in
            leq :: store
        end
        handle Tautology => store
    end

  fun leq_split i store =
      let fun aux neg_set pos_set none_set arg = case arg of 
              [] => (neg_set, pos_set, none_set)
            | leq :: rest =>
                  if (leq $ i) < 0 then
                      aux (leq :: neg_set) pos_set none_set rest
                  else if (leq $ i) > 0 then
                      aux neg_set (leq :: pos_set) none_set rest
                  else
                      aux neg_set pos_set (leq :: none_set) rest

          fun auxpos store neg arg = case arg of
              [] => store
            | pos :: rest => auxpos (leq_combine i neg pos store) neg rest

          fun auxnegpos store pos_set arg = case arg of
              [] => store
            | neg :: rest => auxnegpos (auxpos store neg pos_set) pos_set rest

          val (neg_set, pos_set, none_set) = aux [] [] [] store
      in
          auxnegpos none_set pos_set neg_set
      end



fun store_solve n store =
  let
      val _ = number_of_variables := n

      fun aux store arg = case arg of
          [] => store
        | leq :: rest =>
              let in 
                  let val _ = leq_first leq
                      val _ = leq_norm leq
                  in
                      aux (leq :: store) rest
                  end
                  handle Tautology => aux store rest
              end
              
      val store = aux [] store
                  
      fun aux arg = case arg of
          store as (_ :: _)  => aux (leq_split (leq_least store) store)
        | _ => show_store "Unsolvable: store_solve:\n" store
  in
      aux store
  end

end
