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
(* File: Datasorts.sml
 * Author: Joshua Dunfield
 * Contents: Datasort refinements.
 *)

(*
  Datasort symbols are TC.syms.

  `datasort' declarations simultaneously introduce datasorts
      and define the `kernel' of the subsort relation (before
      reflexive-transitive closure).

  Datatype declarations are unchanged.
   
  Our datasort machinery is very simple,  because we make the programmer
     do all the work: the refinement relation must be written out by hand.
     We deign only to take the reflexive-transitive closure of what is given.
*)

signature DATASORTS = sig
  
  type datasort = TC.sym
  type relation
  
  val reset : unit -> unit
  val printAll : unit -> unit
 
  val includeType : TC.sym -> unit
  val addDatasort : TC.sym * datasort -> unit
  val addPair : datasort * datasort -> unit
  val refines : datasort -> TC.sym option
  val blitheRefines : datasort -> TC.sym   (* identity if datasort not a refinement of anything *)
  val relationOf : TC.sym -> relation
  
  structure Relation : PR where type t = relation

  val compatible : datasort * datasort -> bool
  exception Incomparable
  val subsort : datasort * datasort -> bool   (* Raises Incomparable if arguments not refinements of same type *)
  val blitheSubsort : datasort * datasort -> bool  (* Just returns false if arguments not refinements of same type *)

end


(* The recommended abbreviation for the structure Datasorts is DS. *)

structure Datasorts :> DATASORTS = struct
  
  structure ISE = IntStatistEnv

  exception Incomparable

  type datasort = TC.sym
  datatype relation = Relation of {pairs : (datasort * datasort) list}

  val refinesEnv : TC.sym ISE.env ref = ref (ISE.empty ())
  val env : relation ref ISE.env ref = ref (ISE.empty ())

  fun reset () =
      (refinesEnv := ISE.empty();
       env := ISE.empty())

  fun includeType tc =
      case ISE.get (!env) (TC.toInt tc) of
          SOME relation => ()
        | NONE => (let val relation = ref (Relation{pairs= []})
                       val _ = env := ISE.extend (!env) [(TC.toInt tc, relation)]
                       val _ = refinesEnv := ISE.extend (!refinesEnv) [(TC.toInt tc, tc)]
                   in () end)

  fun addDatasort (tc, d) =
      let val d = TC.toInt d
      in
          case ISE.get (!refinesEnv) d of
              NONE => let val _ = ISE.extend (!refinesEnv) [(d, tc)] in () end
            | SOME tc' => if tc = tc' then () else raise Option (* XXX *)
      end

  fun refines d = ISE.get (!refinesEnv) (TC.toInt d)

  fun blitheRefines d =
      case refines d of
          NONE => d
        | SOME tc => tc
  
  fun relationOf tc = ! (Option.valOf (ISE.get (!env) (TC.toInt tc)))

  fun hoist d1 d2 = 
      let val tc1 = refines d1
          val tc2 = refines d2
      in
          case (tc1, tc2) of
                  (SOME tc1, SOME tc2) => if tc1 = tc2 then tc1 else raise Incomparable
                | _ => raise Incomparable
      end

  fun addPair (d1, d2) =
      let val tc = hoist d1 d2
          val relation as ref (Relation{pairs= pairs}) =
              case ISE.get (!env) (TC.toInt tc) of
                  SOME relation => relation
                | NONE => raise Option   (* XXX *)
(*
   P   ,   d1,d2

   for all d2,X in P add d1,X
   for all Y,d1 in P add Y,d2
*)
          fun extender (da, db) = if da = d2 then SOME(d1, db)
                                  else if db = d1 then SOME(da, d2)
                                       else NONE
          val extension =
              if d1 = d2 then []
              else (d1, d2) :: (List.mapPartial extender pairs)
      in
          relation := Relation {pairs= MyList.elimDups(extension @ pairs)}
      end

  structure Relation : PR = struct
      type t = relation
      fun pairToString (d1, d2) = "(" ^ TC.toShortString d1 ^ ", " ^ TC.toShortString d2 ^ ")"
      fun toString (Relation{pairs}) =
          "{" ^ Separate.list ", " (map pairToString pairs) ^ "}"
  end

      fun subsort (d1, d2) =   (* Raises Incomparable if arguments not refinements of same type *)
          let val tc = hoist d1 d2
              val Relation{pairs= pairs} = relationOf tc
          in
              (d1 = d2) orelse (MyList.contains (d1, d2) pairs)
          end

      fun compatible (d1, d2) = 
         (d1 = d2) orelse
          (let val tc1 = refines d1
              val tc2 = refines d2
          in
              case (tc1, tc2) of
                  (SOME tc1, SOME tc2) => tc1 = tc2
                | _ => false
          end)

      fun blitheSubsort (d1, d2) = 
          (compatible (d1, d2)) andalso (subsort (d1, d2))

  fun printAll () =
      let val list = ISE.toList (!env)
      in
          List.app (fn (tc, relation) =>
                    print ("datasort " ^ TC.toString (TC.fromInt tc) ^ " : " ^ Relation.toString (!relation) ^ "\n")) list
      end

end
