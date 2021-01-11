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
signature MYLIST = sig

    val zip3 : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
    val unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

    val contains : ''a -> ''a list -> bool

    val omit : ''a -> ''a list -> ''a list
    val elimDups : ''a list -> ''a list
    val omit' : ('a * 'a -> bool) -> 'a -> 'a list -> 'a list
    val elimDups' : ('a * 'a -> bool) -> 'a list -> 'a list
    
    val transpose : 'a list list -> 'a list list
    
    val disjoint : ''a list -> ''a list -> bool

    (* mapWithCount 1 f [a, b, c] = [f(1,a), f(2, b), f(3, c)] *)
    val mapWithCount : int -> (int * 'a -> 'b) -> 'a list -> 'b list
end


structure MyList :> MYLIST = struct

  fun mapWithCount z f l = case l of
       [] => []
     | x::xs => f(z, x) :: mapWithCount (z + 1) f xs

  fun zip3 arg = case arg of
          ([], [], []) => []
        | (x::xs, y::ys, z::zs) => (x, y, z) :: zip3 (xs, ys, zs)
        | (_, _, _) => raise ListPair.UnequalLengths

  fun unzip3 arg = case arg of
      [] => ([], [], [])
    | (x, y, z) :: rest =>
          let val (xs, ys, zs) = unzip3 rest
          in
              (x::xs, y::ys, z::zs)
          end

  fun contains x xs =
      List.exists (fn x' => x = x') xs

  fun omit y xs = case xs of
          [] => []
        | x::xs =>
               if x = y then
                   omit y xs
               else
                   x :: (omit y xs)

  fun elimDups xs = case xs of
           [] => []
         | x::xs =>
               (x :: omit x (elimDups xs))

  fun omit' eq y xs = case xs of
          [] => []
        | x::xs =>
               if eq (x, y) then
                   omit' eq y xs
               else
                   x :: (omit' eq y xs)

  fun elimDups' eq xs = case xs of
           [] => []
         | x::xs =>
               (x :: omit' eq x (elimDups' eq xs))

  fun transpose [] = []
    | transpose (column :: columns)  =
       let fun nth n list = List.nth (list, n)
       in
           List.tabulate (length column, fn n => map (nth n) (column :: columns))
       end

  fun disjoint xs ys = not (List.exists (fn x => contains x ys) xs)

end
