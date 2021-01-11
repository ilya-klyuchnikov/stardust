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
signature COERCION = sig

  type t

  val identity : t

  val arr : t * t -> t

  val last : t -> t
  val cons : t * t -> t

  val topR : t

  val sectR : t * t -> t
  val sectL1 : t -> t
  val sectL2 : t -> t

  val unionL : t * t -> t
  val unionR1 : t -> t
  val unionR2 : t -> t
  
  val compile : Sdml.distinguished -> Location.location -> t -> Sdml.locexp
  val compileWith : Sdml.distinguished -> t -> Sdml.locexp -> Sdml.locexp

  val toString : t -> string

  val destultify : t -> t    (* turns tuples of Identity into Identity *)

(* utility functions not inherently tied to the coercion type *)
  val mkCase : Sdml.distinguished
                   -> Sdml.locexp
                   -> (Sdml.pv -> Sdml.locexp) * (Sdml.pv -> Sdml.locexp)
                   -> Sdml.exp

end (* COERCION *)

structure Coercion :> COERCION = struct

fun mkCase (distinguished : Sdml.distinguished) scrutinee (branch1, branch2) =
    let val x1 = PV.fresh "x1"
        val x2 = PV.fresh "x2"
        val inl = #inl_pv distinguished
        val inr = #inr_pv distinguished
        val arm1 = Sdml.Arm (Sdml.CtorPattern (inl, SOME (Sdml.VarPattern x1)), branch1 x1)
        val arm2 = Sdml.Arm (Sdml.CtorPattern (inr, SOME (Sdml.VarPattern x2)), branch2 x2)
    in
        Sdml.Case (scrutinee, [arm1, arm2])
    end

datatype t =
    Identity
  | Arr of t * t
  | Tuple of t list
  | TopR
  | SectL1 of t
  | SectL2 of t
  | SectR of t * t
  | UnionL of t * t
  | UnionR1 of t
  | UnionR2 of t

fun toString t = case t of
    Identity => "Identity"
  | Arr (t1, t2) => "Arr(" ^ toString t1 ^ ", " ^ toString t2 ^")"
  | Tuple ts => "Tuple[" ^ Separate.list ", " (List.map toString ts) ^ "]"
  | TopR => "TopR"
  | SectL1 t => "SectL1(" ^ toString t ^ ")"
  | SectL2 t => "SectL2(" ^ toString t ^ ")"
  | SectR (t1, t2) => "SectR(" ^ toString t1 ^ ", " ^ toString t2 ^")"
  | UnionL (t1, t2) => "UnionL(" ^ toString t1 ^ ", " ^ toString t2 ^")"
  | UnionR1 t => "UnionR1(" ^ toString t ^ ")"
  | UnionR2 t => "UnionR2(" ^ toString t ^ ")"


fun destultify c =
  let val f = destultify
  in 
      case c of
          Identity => Identity
        | Arr (t1, t2) => Arr (f t1, f t2)
        | Tuple ts =>
              let val ts = List.map f ts
              in
                  if List.all (fn Identity => true | _ => false) ts then
                      Identity
                  else
                      Tuple ts
              end
        | TopR => TopR
        | SectL1 t => SectL1 (f t)
        | SectL2 t => SectL2 (f t)
        | SectR (t1, t2) => SectR (f t1, f t2)
        | UnionL (t1, t2) => UnionL (f t1, f t2)
        | UnionR1 t => UnionR1 (f t)
        | UnionR2 t => UnionR2 (f t)
  end


val identity = Identity

fun arr (c1, c2) = Arr (c1, c2)

fun last c = Tuple [c]
fun cons (c, Tuple cs) = Tuple (c::cs)
  | cons (c, Identity) = Tuple (c :: [Identity])
(*         (print ("Coercion.cons: called with tail = " ^ toString tail ^ "\n");
          raise Match)
*)

val topR = TopR

fun sectR (c1, c2) = SectR (c1, c2)

fun sectL1 c = SectL1 c
fun sectL2 c = SectL2 c

fun unionL (c1, c2) = UnionL (c1, c2)
fun unionR1 c = UnionR1 c
fun unionR2 c = UnionR2 c


fun heart (distinguished : Sdml.distinguished) loc c x =
  let val bind = bind distinguished
      val heart = heart distinguished
  in
        case c of
          Identity => x

        | Arr (c1, c2) =>
            let val x1 = PV.fresh "x1"
                val x1exp = (loc, Sdml.Var x1)
            in
                (loc, Sdml.Fn (x1, bind c1 (loc, Sdml.App (x, heart loc c2 x1exp))))
            end

        | Tuple cs =>
             let fun compile_n n cs = case cs of
                     [] => []
                   | c::cs => ((loc, Sdml.Proj (Int.toString n, heart loc c x))) :: (compile_n (n + 1) cs)
             in
                 (loc, Sdml.Tuple (compile_n 1 cs))
             end

        | TopR => (loc, Sdml.Tuple [])

        | SectL1 c => 
             bind c (loc, Sdml.Proj ("1", x))
        | SectL2 c => 
             bind c (loc, Sdml.Proj ("2", x))

        | SectR (c1, c2) => 
             (loc, Sdml.Tuple [heart loc c1 x, heart loc c2 x])

        | UnionL (c1, c2) =>
             (loc, mkCase distinguished x (fn x1 => heart loc c1 (loc, Sdml.Var x1),
                                           fn x2 => heart loc c2 (loc, Sdml.Var x2)))

        | UnionR1 c =>
             (loc, Sdml.Conapp (#inl_pv distinguished, heart loc c x))

        | UnionR2 c =>
             (loc, Sdml.Conapp (#inr_pv distinguished, heart loc c x))
  end

and bind distinguished c (loc, exp) =
   let val c = destultify c
       val x = PV.fresh "x"
       val xexp = (loc, Sdml.Var x)
       val binding = (loc, Sdml.Dec(x, Sdml.ValKW, (loc, exp)))
   in
     (loc, Sdml.Let ([binding],
                    heart distinguished loc c xexp))
   end



fun compile distinguished loc c =
   let val x = PV.fresh "x"
       val xexp = (loc, Sdml.Var x)
       val c = destultify c
   in
       (loc, Sdml.Fn (x, heart distinguished loc c xexp))
   end
     
fun compileWith distinguished c (loc, exp) =
   bind distinguished c (loc, exp)


end (* Coercion *)
