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
signature PATTERNS = sig
  
  type pattern = Sdml.pattern

  (* analyze:
        given a function `otherCtors c' that, given a constructor c of datatype t,
         returns all other constructors of t,

        and a pair

            (domain : pattern,
             pattern : pattern)

        returns another pair
        
            (remaining : pattern,
             relevant : pattern)

        where

            remaining  =  domain \minus pattern
            relevant   =  pattern \intersection domain
  *)
  val analyze : (Sdml.pv -> (Sdml.pv * (unit option)) list)
                   -> pattern * pattern
                 -> pattern * pattern

  val splitIntoConjuncts : (Sdml.pv -> Sdml.pv list)
                        -> pattern
                      -> pattern

  val weight : Sdml.pattern -> int
  
  val includes : pattern * pattern -> bool    (* true iff pat1 matches at least the values pat2 does *)
(*  val improve : pattern list -> pattern list *)
  val improve : pattern -> pattern 


end



structure Patterns :> PATTERNS = struct
  
  open Sdml
  structure P = Print

  type pattern = Sdml.pattern
 
  fun splitIntoConjuncts splitFn p = case p of

       VarPattern x => VarPattern x
     | WildPattern => WildPattern
     | StringPattern string => StringPattern string
     | IntPattern int => IntPattern int
     
     | CtorPattern (c, p0) =>
           let val p0split = case p0 of
                                          NONE => NONE
                                        | SOME p0 => SOME (splitIntoConjuncts splitFn p0)
               val csplit = splitFn c
           in
               OrPattern (List.map (fn c1 => CtorPattern (c1, p0split)) csplit)
           end

    | TuplePattern ps => TuplePattern (List.map (splitIntoConjuncts splitFn) ps)

    | RecordPattern (string, p0) =>
           let val p0split = splitIntoConjuncts splitFn p0
           in
               RecordPattern (string, p0split)
           end

    | AsPattern (x, p0) =>
           let val p0split = splitIntoConjuncts splitFn p0
           in
               AsPattern (x, p0split)
           end
      

(* fold : (pattern -> pattern) -> pattern -> pattern *)
  fun fold f p = case p of
       WildPattern => f p
     | VarPattern x => f p
     | CtorPattern (c, p0) => f (CtorPattern (c, Option.map (fold f) p0))
     | TuplePattern ps => f (TuplePattern (List.map (fold f) ps))
     | OrPattern ps => f (OrPattern (List.map (fold f) ps))
     | AsPattern (x, p0) => f (AsPattern (x, fold f p0))
     | StringPattern _ => f p
     | IntPattern _ => f p

  fun burn_map f list = case list of
      [] => SOME []
    | x :: xs => 
          let in case f x of
             NONE => NONE
           | SOME x' =>
                    let in case burn_map f xs of
                         NONE => NONE
                       | SOME xs' => SOME (x' :: xs')
                    end
          end

(* burn : (pattern -> pattern option) -> pattern -> pattern option *)
  fun burn (f : pattern -> pattern option) (p : pattern) : pattern option =
          let val burn = burn : (pattern -> pattern option) -> pattern -> pattern option
in
case p of
       WildPattern => f p
     | VarPattern x => f p
     | CtorPattern (c, p0) =>
          let in case p0 of
              NONE => f (CtorPattern (c, NONE))
            | SOME p0 =>
                   let in case burn f p0 of
                              NONE => NONE
                            | SOME p0 => f (CtorPattern (c, SOME p0))
                   end
          end
     | TuplePattern ps =>
          let in case burn_map f ps of
              NONE => NONE
            | SOME ps => f (TuplePattern ps)
          end
     | OrPattern ps =>
          let in case burn_map f ps of
              NONE => NONE
            | SOME ps => f (OrPattern ps)
          end
     | AsPattern (x, p0) =>
          let val burn = burn : (pattern -> pattern option) -> pattern -> pattern option
          in case burn f p0 of
              NONE => NONE
            | SOME p0 => f (AsPattern (x, p0))
          end

     | StringPattern _ => f p
     | IntPattern _ => f p
end


(* full_burn : (pattern -> pattern option) -> pattern -> pattern *)
  fun full_burn f p = case burn f p of
       SOME p => p
     | NONE => OrPattern []

  fun stripAs p =
      fold (fn VarPattern x => WildPattern
             | AsPattern (x, p0) => p0
             | OrPattern [one] => one
             | p => p)
           p

(*  
  fun elimOrDups pat =
      full_burn (fn
               OrPattern [] => NONE
          | OrPattern ps => SOME (OrPattern (MyList.elimDups ps))
          | p => SOME p)
         pat
*)

  fun whittle p =
   case p of
       WildPattern => SOME p
     | VarPattern x => SOME p
     | CtorPattern (c, p0) =>
          let in case p0 of
              NONE => SOME (CtorPattern (c, NONE))
            | SOME p0 =>
                   let in case whittle p0 of
                              NONE => NONE
                            | SOME p0 => SOME (CtorPattern (c, SOME p0))
                   end
          end
     | TuplePattern ps =>
          Option.map TuplePattern (burn_map whittle ps)
     
     | OrPattern ps =>
          let in case List.mapPartial whittle ps of
                     [] => NONE
                   | list => SOME (OrPattern list)
          end
     | AsPattern (x, p0) =>
          let in case whittle p0 of
              NONE => NONE
            | SOME p0 => SOME (AsPattern (x, p0))
          end
     
     | StringPattern _ => SOME p
     | IntPattern _ => SOME p
  
  val elimOrDups = whittle
  
  fun full_burn p = case whittle p of
       SOME p => p
     | NONE => OrPattern []



  fun weight p =
      let val count = ref 0
      in
          fold (fn p => (count := !count + 1; p)) p;
          !count
      end

  fun check p =
      fold (fn AsPattern (x1, AsPattern (x2, p)) =>  if x1 = x2 then raise Option else p
             | p => p) p


  fun analyze otherCtors (domain, p) =
      let val ps = full_burn domain
          val analyze = fn arg => ((fn (domain, qs) => (full_burn domain, full_burn qs)) (analyze otherCtors arg))
          val ps = stripAs ps

          (* mkCtorPattern:
               If c nullary,     returns pattern "c" = CtorPattern(c, NONE);
               If c non-nullary, returns pattern "c _" = CtorPattern(c, SOME WildPattern)
         *)
          fun mkCtorPattern (c, arg) =
              CtorPattern(c, Option.map (fn () => WildPattern) arg)
          
          val result = 
                    case (ps, p) of
                        (OrPattern [], p) =>
                             ( (* {} \ p = *)  OrPattern [],
                               (* p && {} = *) OrPattern [])
                      
                      | (OrPattern [one], p) =>
                            analyze (one, p)

                      | (p, OrPattern []) =>
                           (p, OrPattern [])

                      | (p, OrPattern (p1 :: ps)) => 
                            let val (difference, intersection1) = analyze (p, p1)
                                val (difference, intersection2) = analyze (difference, OrPattern ps)
                            in
                                (difference, OrPattern [intersection1, intersection2])
                            end
                      
                      | (OrPattern (ps as _ :: _ :: _), p) =>
                          (* ps =[p1 | ... | pn]   for n >= 2 *)
                            let val (qsStar, qs) = ListPair.unzip (List.map (fn pk => analyze (pk, p)) ps)
                            in
                                ( (* (p1 U ... U pn) \ p = (p1 \ p) U ... U (pn \ p) *)  OrPattern qsStar,
                                 (* (p && (p1 U ... U pn) = (p && p1) U ... U (p && pn) *) OrPattern qs)
                            end

                      (* length ps = 0 and length ps >= 2 covered;
                       remaining branches are for length ps = 1. *)

                      | (d, AsPattern(x, p0)) =>
                            let val ( (* d \ p0 = *) qsStar,
                                      (* p0 && d = *) qs)
                                    =
                                    analyze (d, p0)
                            in
                                ( (* d \ (x as p0) = d \ p0 = *) qsStar,
                                 AsPattern(x, qs)   (* restore the `as' *)
                                )
                            end

                      | (d, VarPattern x) =>
                             ( (* d \ x = {} = *) OrPattern [],
                               (* x && d = (x as d) = *) AsPattern (x, d))
                      | (d, WildPattern) =>
                             ( (* d \ _ = {} = *) OrPattern [],
                              (* d && _ = d = *) d)

                      | (WildPattern, CtorPattern (c, NONE)) =>
                            let val otherPats = List.map mkCtorPattern (otherCtors c)
                            in
                                ( (* _ \ c = (c1 <_>) U ... U (cn <_>) = *) OrPattern otherPats,
                                 CtorPattern(c, NONE))
                              (* (where c1, ..., cn are the other constructors of c's datatype,
                            and "<_>" is either nothing or "_" according to whether each
                            other constructor is nullary or non-nullary *)
                            end

                      | (WildPattern, CtorPattern (c, SOME p0)) =>
                            let 
                                val otherPats = List.map mkCtorPattern (otherCtors c)
                                val (qsStar, qs) = analyze (WildPattern, p0)
                                val (qsStar, qs) = (CtorPattern(c, SOME qsStar),
                                                               CtorPattern(c, SOME qs))
                            in
                                (OrPattern (qsStar :: otherPats),
                                 qs)
                            end

                      | (p1 as CtorPattern(c1, NONE),  p2 as CtorPattern(c2, NONE)) => 
                            if c1 <> c2 then
                                (p1, OrPattern [])
                            else
                                (OrPattern [], p2)

                      | (p1 as CtorPattern(c1, NONE),  p2 as CtorPattern(c2, SOME p20)) => 
                            if c1 <> c2 then (p1, OrPattern [])
                            else
                               (print ("c1 = " ^ PV.toString c1 ^ ",  c2 = " ^ PV.toString c2 ^ "\n");
                                print ("p1 = " ^ P.p P.printPat p1 ^ ";  p2 = " ^ P.p P.printPat p2 ^ "\n");
                                raise Option  (* Should be impossible: a ctor cannot be both nullary and non-nullary *) )

                      | (p1 as CtorPattern(c1, SOME p10),  p2 as CtorPattern(c2, p20opt)) =>
                            if c1 <> c2 then
                                (p1, OrPattern [])
                            else
                                let val c = c1    (* c = c1 = c2 *)
                                in
                                    case p20opt of
                                        NONE => (print ("constructor " ^ P.p P.printPat p2 ^ " used as if nullary\n"); raise Option)
                                      | SOME p20 => 
                                            let
                                                fun apply_c q0 = CtorPattern(c, SOME q0)
                                                val (qsStar, qs) = analyze (p10, p20)
                                            in
                                                (apply_c qsStar,
                                                 apply_c qs)
                                            end
                                end

                      | (WildPattern, TuplePattern p0s) =>
                            analyze (TuplePattern (List.map (fn _ => WildPattern) p0s), TuplePattern p0s)

                      | (TuplePattern [], TuplePattern []) =>
                            (OrPattern [], TuplePattern [])

                      | (TuplePattern p1s, TuplePattern p2s) =>
                            let fun ggg ([], []) = ([], [])
                                  | ggg (p1::p1s, p2::p2s) =
                                        let val (headDiff, headInt) = analyze (p1, p2)
                                                    (*  fun printps ps = "(" ^ Separate.comma (map patternToString ps) ^ ")"
                                            val _ = print ("hStars = " ^ printps hStars ^" \n")
                                            val _ = print ("hs = " ^ printps hs ^" \n")
                                            *)
                                            val (tailDiffs, tailInt) = ggg (p1s, p2s)
                                                    (*
                                            val _ = print ("tStars = " ^ Separate.list ",  " (map printps tStars) ^ "\n")
                                            val _ = print ("ts = " ^ Separate.list ",  " (map printps ts) ^" \n")
                                            *)
                                        in
                                            ((headDiff :: p1s)
                                               ::
                                               List.map (fn tailDiff => headInt :: tailDiff) tailDiffs,
                                             headInt :: tailInt)
                                        end
                                  | ggg (_, _) = raise Option (* arities inconsistent: pattern ill-typed *)
                                val (qStars, qs) = ggg (p1s, p2s)
                            in
                                (OrPattern (List.map (fn qStar => TuplePattern qStar) qStars),
                                 TuplePattern qs)
                            end

                      | (WildPattern,  p2 as StringPattern s2) => 
                            (WildPattern, p2)

                      | (p1 as StringPattern s1,  p2 as StringPattern s2) => 
                            if s1 <> s2 then
                                (p1, OrPattern [])
                            else
                                (OrPattern [], p2)

                      | (WildPattern,  p2 as IntPattern s2) => 
                            (WildPattern,  p2)

                      | (p1 as IntPattern i1, p2 as IntPattern i2) => 
                            if i1 <> i2 then
                                (p1, OrPattern [])
                            else
                                (OrPattern [], p2)

                      | (ps, p2) =>
                              (print ("analyze FAIL: "
                                      ^ patternToString ps ^ ",    "
                                      ^ patternToString p2 ^ "\n");
                               raise Option)
                              
          val (remaining, intersection) = result
          val (remaining, intersection) = (check (full_burn remaining), check (full_burn intersection))
        (*
          val _ = print ("analyze:  " ^ patternToString ps ^ "  \\and&  " ^ patternToString p ^ " = \n")
          val _ = print ("     --:  " ^ patternToString remaining ^ " <-\\ &->  " ^ patternToString intersection ^ " = \n\n")
       *)
      in
          (remaining, intersection)
      end

  val bogusVar = PV.fromInt 0
  val p0 = WildPattern
  val c1 = PV.fromInt 1111
  val c2 = PV.fromInt 2222
  val c3 = PV.fromInt 3333
  fun otherCtors c =
      let val c1x = (c1, SOME ())
          val c2x = (c2, SOME ())
          val c3x = (c3, NONE)
      in
      if c = c1 then [c2x, c3x]
      else if c = c2 then [c1x, c3x]
      else if c = c3 then [c1x, c2x]
      else raise Option
      end

  fun testanalyze (ps, p) = 
      let val _ = print ("input:       " ^ patternToString ps ^ "; \n")
          val _ = print ("against  " ^ patternToString p ^ ".\n")
          val (domain, image) = analyze otherCtors (ps, p)
          val _ = print ("difference:  " ^ patternToString domain ^ "; \n")
          val _ = print ("intersection: " ^ patternToString image ^ ".\n$\n")
      in
          ()
      end


(***
  val c1pat = CtorPattern(c1, SOME (WildPattern))
  val c2pat = CtorPattern(c2, SOME (WildPattern))
  val c3pat = CtorPattern(c3, NONE)
  val _ = testanalyze (p0, c1pat)
  val _ = testanalyze (p0, c2pat)
  val _ = testanalyze (TuplePattern[WildPattern, WildPattern], TuplePattern[c1pat, c2pat])
  val _ = testanalyze (p0, TuplePattern[c1pat, c2pat])
  val _ = testanalyze (p0, TuplePattern[c1pat, c2pat])
  
  val _ = print "\n\n\n"

  val c1 = PV.fromInt 1
  val c2 = PV.fromInt 2
  val c1pat = CtorPattern(c1, SOME (WildPattern))
  val c2pat = CtorPattern(c2, SOME (WildPattern))
  fun otherCtors c =
      let val c1x = (c1, SOME ())
          val c2x = (c2, SOME ())
      in
      if c = c1 then [c2x]
      else if c = c2 then [c1x]
      else raise Option
      end

  val xx = PV.fromInt 55
  val _ = testanalyze (c1pat, AsPattern(xx, WildPattern))
  
  val _ = print "\n\n"
  val _ = testanalyze (c1pat, WildPattern)
***)

  fun includes (p1, p2) = case (p1, p2) of
      (WildPattern, _) => true
    | (AsPattern(_, p1'), p2) => includes (p1', p2)
    | (p1, AsPattern (_, p2')) => includes (p1, p2')
    | (VarPattern _, _) => true
    | (CtorPattern(c1, NONE), CtorPattern(c2, NONE)) =>
          (c1 = c2)
    | (CtorPattern(c1, SOME p1), CtorPattern(c2, SOME p2)) =>
          (c1 = c2) andalso includes (p1, p2)
    | (StringPattern s1, StringPattern s2) =>
          (s1 = s2)
    | (IntPattern i1, IntPattern i2) =>
          (i1 = i2)
    | (TuplePattern ps1, TuplePattern ps2) => 
          List.all includes (ListPair.zip (ps1, ps2))
    | (_, WildPattern) => false
    | (_, VarPattern _) => false
    | (_, _) => false

  fun improve' ps = case ps of
     [] => []
   | p1 :: ps =>
       if List.exists (fn p => includes(p, p1)) ps then
           improve' ps
       else
           p1 :: improve' ps
  
  fun improve ps = List.rev (improve' (List.rev (improve' ps)))

  datatype inclusion = CONTAINS | IN | BOTH | NO
  
  fun inclusion (p1, p2) = case (p1, p2) of
      (WildPattern, WildPattern) => BOTH
(*    | (VarPattern x, WildPattern) => BOTH
    | (VarPattern x, VarPattern y) => BOTH
    | (WildPattern, VarPattern x) => BOTH
    | (VarPattern _, _) => CONTAINS
*)
    | (WildPattern, _) => CONTAINS
    | (_, WildPattern) => IN
(*    | (_, VarPattern _) => IN
    | (AsPattern(_, p1'), p2) => inclusion (p1', p2)
    | (p1, AsPattern (_, p2')) => inclusion (p1, p2')
*)
    | (CtorPattern(c1, NONE), CtorPattern(c2, NONE)) =>
          if c1 = c2 then BOTH else NO
    | (CtorPattern(c1, SOME p1), CtorPattern(c2, SOME p2)) =>
          if c1 = c2 then inclusion (p1, p2) else NO
    | (StringPattern s1, StringPattern s2) =>
          if s1 = s2 then BOTH else NO
    | (IntPattern i1, IntPattern i2) =>
          if i1 = i2 then BOTH else NO
    | (TuplePattern ps1, TuplePattern ps2) => 
          let fun traverse (ps1, ps2) = case (ps1, ps2) of
                    ([], []) => BOTH
                  | (p1::ps1, p2::ps2) => 
                          let
                              fun all_contain (ps1, ps2) = case (ps1, ps2) of
                                    ([], []) => CONTAINS
                                  | (p1::ps1, p2::ps2)  =>
                                        let in case inclusion (p1, p2) of
                                                   CONTAINS => all_contain (ps1, ps2)
                                                 | BOTH => all_contain (ps1, ps2)
                                                 | _ => NO
                                        end
                              fun all_in (ps1, ps2) = case (ps1, ps2) of
                                    ([], []) => IN
                                  | (p1::ps1, p2::ps2)  =>
                                        let in case inclusion (p1, p2) of
                                                   IN => all_in (ps1, ps2)
                                                 | BOTH => all_in (ps1, ps2)
                                                 | _ => NO
                                        end
                          in
                              case inclusion (p1, p2) of
                                     CONTAINS => all_contain (ps1, ps2)
                                   | IN => all_in (ps1, ps2)
                                   | BOTH => traverse (ps1, ps2)
                                   | NO => NO
                          end
                  | (_, _) => NO
          in
              traverse (ps1, ps2)
          end
    | (_, _) => NO

(*
 fun inclusion (pi, pj) = if includes (pj, pi) then IN else if includes (pi, pj) then CONTAINS else NO
*)
  fun improve ps =
          let val mutt : pattern option array = Array.fromList (List.map SOME ps)
              val n = Array.length mutt
    (*          val _ = print "improve n = "
              val _ = print (Int.toString n ^ "\n") *)
              fun improve' i j =
                  if j >= n then
                      ()
                  else
                     let val pi = Array.sub (mutt, i)
                         val pj = Array.sub (mutt, j)
                     in
                         case (pi, pj) of
                             (SOME pi, SOME pj) =>
                                let in
                                    case inclusion (pi, pj) of
                                           CONTAINS =>  (* delete pj *)
                                               (Array.update (mutt, j, NONE);
                                                improve' i (j + 1))
                                         | IN =>
                                               (* delete pi *)
                                                   (Array.update (mutt, i, NONE);
                                                    () (* return, all subsequent comparisons would fall into NONE *))
                                         | BOTH => 
                                                   (Array.update (mutt, i, NONE);
                                                    () (* return, all subsequent comparisons would fall into NONE *))
                                         | NO =>
                                                improve' i (j + 1)
                                end
                           | _ => improve' i (j + 1)
                     end
          in
              Array.appi (fn (i, _) => improve' i (i + 1)) mutt;
              Array.foldr (fn (NONE, ps) => ps
                            | (SOME p, ps) => p :: ps) [] mutt
          end

         
      
  val CORE = improve
  fun improve ps =
       let (* val a = CORE ps *)
           val b = CORE ps
       in
           b
       end


(***

(*
c(c1, c2, c3)
c(c1, c2, c4)


[d1, d2, d3]

                 c
               /  \
 [c1,c2,c3]    [c1,c2,c4]
*)

(* trie representation of a union of patterns *)
  datatype node = 
       Wild
     | Ctor of pv * union
     | String of string
     | Int of int
     | Tuple of node list
  withtype union = trie list ref
  
  fun add u p =
      case (u, p) of
          (r as ref ts, p) => r := addl ts p
  
  and addl ts p =
      case (ts, p) of
          ([], p) => [p]
        | (_, WildPattern) => [Wild]
        | (Wild :: _, _) => [Wild]
        
        | (String s1 :: ts2, StringPattern string) => if s1 = string then ts else String s1 :: (addl ts2 p)
        | (Int i1 :: ts2, IntPattern int) => if i1 = int then ts else Int i1 :: (addl ts2 p)
        | ([], StringPattern string) => [String string]
        | ([], IntPattern int) => [Int int]
        
        | (Ctor (c, u) :: ts2, CtorPattern (c0, p0)) =>
              if c = c0 then
                  (add u p0;
                   ts)
              else
                  Ctor (c, u) :: (addl ts2 p)
        
        | (Tuple nodes :: ts, TuplePattern ps) =>
              List.app (ListPair.zip (nodes, ps))

        | (t :: ts, _) => t :: (addl ts p)
  
  and add 


  val add = fn t => fn p => add t (stripAs p)

***)

  fun improve x = x
  
end (* structure Patterns *)
