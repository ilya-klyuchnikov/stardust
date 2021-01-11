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
(* File: Destultify.sml
   Author: Joshua Dunfield
   Contents: Minor destultifications of target expressions:

(*   1.   let decs1 in let decs2 in ... let decsn in e end end ----> let decs1 decs2 ... decsn in e end *) (* bogus because Sdml's let syntax only allows   let ... and ... and ... in end --- accomplishing this in Print.sml instead *)

   2.   let val x1 = y1 in e2 end ----> [y1/x1]e2
       This clearly removes useless "renaming" bindings; it also removes unused bindings to variables.  In practice, these are most of them...

   3.  let val x1 = e1 in x1 end ----> e1

   4.  val x = e ...    ---->  val _ = e ...    *** if x does not appear in ... ***

   History: 2012-01-30 [jcd] -- Created.
*)

signature DESTULTIFY = sig

  val destultify : Sdml.program -> Sdml.program

end

structure Destultify :> DESTULTIFY = struct

  open Sdml

  structure P = Print
(*  structure X = Indexing *)

  datatype hole_tree =
      Leaf of pv * locexp
    | Binary of hole_tree * hole_tree

  fun treeToString t = case t of
      Leaf (pv, exp) => "Leaf (" ^ PV.toString pv ^ ", " ^ "_" ^ ")"
    | Binary (tree1, tree2) => 
          "Binary (" ^ treeToString tree1 ^ ", " ^ treeToString tree2 ^ ")"

  fun process counter stem body =
      let in
          case body of
              (loc, Tuple [e1, e2]) =>
                  let val (tree1, counter) = process counter stem e1
                      val (tree2, counter) = process counter stem e2
                  in
                      (Binary (tree1, tree2),
                       counter)
                  end

            | e =>
                  let
                      val y = PV.fresh (stem ^ "'" ^ Int.toString counter)
                  in 
                      (Leaf (y, e),
                       counter + 1)
                  end
      end

  fun generate loc tree =
      let
      in
          case tree of
              Leaf (x, e) => ([(loc, Dec (x, FunKW, e))], (loc, Var x))
                  
            | Binary (tree1, tree2) => 
                  let val (decs1, tupleage1) = generate loc tree1
                      val (decs2, tupleage2) = generate loc tree2
                  in
                      (decs1 @ decs2,
                       (loc, Tuple [tupleage1, tupleage2])
                      )
                  end
      end

(* flatten_rec_tuples

  example:
     val rec x = (e1, e2)
   --->
     val x = let val rec x1 = e1
                     and x2 = e2
             in
                 (x1, x2)
             end
*)
 
  fun reduce_proj loc x tree e =
      let
          fun process tree exp =
              let val _ = print ("process (x = " ^ PV.toString x
                                 ^ ", tree = " ^ treeToString tree
                                 ^ "): " ^ Print.pExp exp ^ "\n")
              in
                  case exp of
                      Proj (k, (loc, tuple)) =>
                           let in
                               case Int.fromString k of
                                      NONE =>  (* record projection *)
                                         e

                                    | SOME 1 =>
                                           let in case tree of 
                                                      Binary (tree1, _) =>
                                                          process tree1 tuple
                                                    | _ => e
                                           end

                                    | SOME 2 =>
                                           let in case tree of 
                                                      Binary (_, tree2) =>
                                                          process tree2 tuple
                                                    | _ => e
                                           end

                                    | SOME _ (* >2*) =>
                                          e
                           end

                    | Var x' =>
                           let
                               val _ = print ("reduce_proj: Var: " ^ Print.pExp (Var x') ^ "\n")
                           in
                               if x <> x' then e
                               else
                                   let val (_, (loc', tupleage)) = generate loc tree
                                       val _ = print ("reduce_proj: TRIGGER: " ^ Print.pExp (Var x') ^ "\n")
                                   in
                                        tupleage
                                        before
                                        print ("TRIGGER: " ^ Print.pExp tupleage ^ "\n")
                                   end
                           end                          
                    | Anno ((loc, core), anno) =>
                          process tree core
                    | exp => e
              end
      in
          case e of
              Proj _ => process tree e

            | e => e
      end


  fun reduce_projections loc x tree decs =
      SdmlFold.fold_decs (SdmlFold.expSpec (reduce_proj loc x tree)) decs

  fun flatten_rec_tuples dec = 
      case dec of 
          Dec (x, FunKW, body) =>
              let
              in
                  case body of
                      (loc, Tuple elements) =>
                          let val (tree, count) = process 1 (PV.toShortString x) body
                              val (decs, tupleage) = generate loc tree
                              val decs' = reduce_projections loc x tree decs
                              val sublet = Let (decs', tupleage)
                              val _ = print ("SUBLET =  " ^ Print.pExp sublet ^ "\n")
                          in
                              Dec  (x,  ValKW (*don't generate val rec for outer binding *),  (loc, sublet))
                          end
                    | _ => dec
              end
        | dec => dec

  fun destultify (Program(libinfo as Libinfo{primtcs, primops, distinguished},
                          typedecsl,
                          locexp)) = 
      let

(*   2.   let val x1 = y1 in e2 end ----> [y1/x1]e2   *)
          fun transform_exp2 exp =
              case exp of
(*                 Let (decs1, (loc1, Let(decs2, (loc, exp)))) => Let (decs1 @ decs2, (loc, exp)) *)
                  Let ([(loc1, Dec(pv1, kw, (loc2, Var pv2)))],  (loc, body)) =>
                       Subst.rename {from=pv1, to=pv2} body
                       
               | exp => exp


(*   3.  let val x1 = e1 in x1 end ----> e1   *)
          fun transform_exp3 exp =
              case exp of
(*                 Let (decs1, (loc1, Let(decs2, (loc, exp)))) => Let (decs1 @ decs2, (loc, exp)) *)
                  Let ([(loc1, Dec(pv1, kw, (loc2, bound_exp)))],  (loc, Var pv2)) =>
                       if pv1 = pv2 then
                         bound_exp
                       else
                         exp
                       
               | exp => exp

          exception Found
          fun occurs x locexp =
              let fun occurs' exp = case exp of
                    Var y => (if x = y then raise Found else exp)
                  | Lvar y => (if x = y then raise Found else exp)
                  | exp => exp
              in
                (SdmlFold.fold_locexp (SdmlFold.expSpec occurs') locexp;
                 false)
                handle
                  Found => true
              end

(*   4.    *)
          fun transform_dec4 programBody dec = case dec of
                   Dec(x, kw, boundExp) =>
                        if occurs x programBody then
                            dec
                        else
                            Dec(PVExtra.underscore, kw, boundExp)
                 | dec => dec

          val locexp1 = locexp
          val locexp2 = SdmlFold.fold_locexp (SdmlFold.expSpec transform_exp2) locexp1
          val locexp3 = SdmlFold.fold_locexp (SdmlFold.expSpec transform_exp3) locexp2
          val locexp4 = (* SdmlFold.fold_locexp (SdmlFold.decSpec (transform_dec4 locexp3)) *) locexp3
          val locexp5 = SdmlFold.fold_locexp (SdmlFold.decSpec flatten_rec_tuples) locexp4

          val final_locexp = locexp5
      in
          Program(Libinfo{primtcs= primtcs,
                          primops= primops, 
                          distinguished= distinguished},
                  typedecsl,
                  final_locexp)
      end

end
