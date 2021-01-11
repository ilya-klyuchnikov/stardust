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
signature CASE = sig

    type result = Sdml.locexp

    val allPairs : ((int * 'a) * (int * 'a) -> unit) -> 'a option array -> unit
    val allDistinctPairs : ((int * 'a) * (int * 'a) -> unit) -> 'a option array -> unit

    datatype fight_result = SECOND_LOST | FIRST_LOST | NO_LOSER
    val fight_result_toString : fight_result -> string
    val bout  :  ('a * 'a -> fight_result) -> 'a list -> 'a list

    datatype tuple =
       TUP of {rctx : Context.rctx,
               conjunct : Sdml.pv,
               things : (Sdml.tv list * Context.indexassumption list),
               varmap : Context.varmap,  (* renaming from index variables in domain/codomain *back to* original (bound) index variables *)
               constraint : Indexing.constraint,
               domain : Sdml.texp option,
               codomain : Sdml.texp}

    datatype inner_tuple =
       INTUP of {previous : tuple list,
                 ctx : Context.ctx,
                 conjunct : Sdml.pv,
                 varmap : Context.varmap,
                 domainOpt : Sdml.texp option,
                 codomain : Sdml.texp}

    val dprint : (unit -> string) -> unit
    val dprnt : string -> unit

    val tupleToString : tuple -> string
    val tuplesToString : tuple list -> string
    val intupToString : inner_tuple -> string
    val intupsToString : inner_tuple list -> string

    val fastIncompleteSubtype : Sdml.texp -> Sdml.texp -> bool

    val reqSubtype : Subtype.result Context.failure
                     -> Context.rctx * Context.mctx
                     -> Types.texp * Types.texp
                     -> (Subtype.result Context.failure * 
                              (Context.rctx * Context.mctx)
                              -> Subtype.result)
                     -> Subtype.result

    val reqSubtypeFlexing : Subtype.result Context.failure
                            -> Context.rctx * Context.mctx
                            -> Types.texp * Types.texp
                            -> (Subtype.result Context.failure * 
                                     (Context.rctx * Context.mctx)
                                     -> Subtype.result)
                            -> Subtype.result
    val reqProp : 'a Context.failure
                      -> 'b * Context.mctx
                       -> Indexing.constraint
                       -> ('a Context.failure * ('b * Context.mctx) -> 'a)
                       -> 'a
    val suppIndex : 'a * Context.mctx
                    -> Sdml.tv list * Context.indexassumption list
                    -> ('a * Context.mctx -> 'b) -> 'b


    val collect : Context.mctx
                  -> Sdml.texp
                  -> tuple list
                  -> (inner_tuple list -> Subtype.result)
                  -> result


    val toXi'' : (unit -> Subtype.result)
                 -> (Context.rctx * Context.mctx) * Types.texp * Types.texp * Types.texp * Sdml.pattern
                 -> Subtype.result Context.failure
                 -> tuple list
                 -> (('a -> Subtype.result) * Context.option_track -> Subtype.result)
                 -> Subtype.result

    val ff :    (result Context.failure
                 -> Context.track
                 -> (Subtype.result Context.failure * Context.track list -> Subtype.result)
                 -> result)
           ->
               (
                ('a * Context.mctx) * Sdml.pattern option *  (string -> result) * Types.texp
               )
           -> result Context.failure
           -> inner_tuple
           -> (result Context.failure * Context.xi_track list -> result)
           -> result

end (* signature CASE *)


structure Case :> CASE = struct

    open Silly
    
    open Sdml
    open Context
  infix 5 %%
  infix 5 $+
  infix 5 ++
  infix 5 +-
  infix 5 +--+
  infix 5 +~~+
    structure X = Indexing
    structure P = Print
    structure DS = Datasorts

    type result = Sdml.locexp
    

    val {dprint, dprnt} =
            Debug.register {full_name= "Case",
                            short_name= "Case"}

    fun t2str texp = P.pTexp texp
    fun topt2str texp = case texp of NONE => "NONE" | SOME texp => P.pTexp texp



    val ctorPatternOrNondet : int ref = ref 0

    fun allSols mctx f k =
        let val r = ref []
        in
            f (fn _ => k (!r))
              (fn (failure, result) =>
                  (r := result :: !r;
                   raise_Dead failure mctx (fn () => "allSols")))
        end

    fun concatSolsAppliedToList acc mctx xs f k =
        case xs of
            [] => k acc
          | (x as (_, x_mctx)) :: xs => 
              let in
                  case getState x_mctx of
                    NONE => (print "check_pattern.CtorPattern.concatSolsAppliedToList: getState returned NONE\n";
                             concatSolsAppliedToList acc mctx xs f k)
                  | SOME _ =>  
                        allSols mctx (f x)
                        (fn theseR => concatSolsAppliedToList (theseR @ acc) mctx xs f k)
              end


    datatype tuple =
       TUP of {rctx : rctx,
               conjunct : pv,
               things : (tv list * indexassumption list),
               varmap : varmap,  (* renaming from index variables in domain/codomain *back to* original (bound) index variables *)
               constraint : X.constraint,
               domain : texp option,
               codomain : texp}

    datatype inner_tuple =
       INTUP of {previous : tuple list,
                 ctx : ctx,
                 conjunct : pv,
                 varmap : varmap,
                 domainOpt : texp option,
                 codomain : texp}


    fun tupleToString (TUP {rctx,
                            conjunct,
                            things= (tvs, assns),
                            constraint=W,
                            varmap,
                            domain,
                            codomain}) =
                    "TUP (" (* ^ rctxToString rctx ^ ",\n     " ^ *) 
                      ^ "conjunct constructor " ^ PV.toString conjunct ^ "; "
                      ^ Context.indexToString assns
         (* ^ ",\n     " *) ^ X.Constraint.toString W
         ^ ",     " ^ (case domain of NONE => "---nullary---" | SOME domain => t2str domain)
           ^ ",   " ^ t2str codomain
         ^ ")  "

    fun tuplesToString tups = 
      Separate.list "\n" (List.map tupleToString tups) ^ "\n"



    fun intupToString (INTUP {ctx,
                            conjunct,
                            domainOpt,
                            codomain,
                            ...}) =
                    "INTUP (" (* ^ rctxToString rctx ^ ",\n     " ^ *) 
                      ^ "conjunct " ^ PV.toString conjunct ^ "; "
         ^ (case domainOpt of NONE => "---nullary---" | SOME domain => t2str domain)
           ^ ",   " ^ t2str codomain
         ^ ")  "

    fun intupsToString tups = 
      Separate.list "\n" (List.map intupToString tups) ^ "\n"

    
    
    fun allPairs f arr =
        newArray_appi
            (fn (x1, elem1) =>
                let in 
                    case elem1 of
                        NONE => ()
                      | SOME elem1 =>
                            newArray_appi
                                (fn (x2, elem2) =>
                                    let in
                                        case elem2 of NONE => ()
                                                    | SOME elem2 => 
                                                      f ((x1, elem1), (x2, elem2))
                                    end)
                                arr
                end)
            arr

    fun allDistinctPairs f arr =
        allPairs (fn (arg as ((x1, elem1), (x2, elem2))) =>
                          if x1 = x2 then ()
                          else f arg) arr




    fun fastIncompleteSubtype s1 s2 =
           let fun f (s1, s2) = case (s1, s2) of
                    (Product A1s, Product A2s) =>     (List.length A1s = List.length A2s) andalso (List.all f (ListPair.zip (A1s, A2s)))
                  | (Tycon(tc1, i1, []), Tycon(tc2, i2, [])) =>          (i1 = i2)  andalso  (  tc1 = tc2  orelse  DS.blitheSubsort(tc1, tc2)  )
                  (*PPP*) (* Need polymorphic case (devolve to fastIncompleteSubtype with appropriate variances on each...) *)
                  | (Exis(a1, sort1, A1), Exis(a2, sort2, A2)) =>   (sort1 = sort2) andalso
                                                                                                      let val A2' = Types.substIndex [(a2, X.Evar a1)] A2
                                                                                                      in f (A1, A2') end
                  | (_, _) => false   (*PPP*) (* print warning? *)
           in
               f (s1, s2)
           end


    datatype fight_result = SECOND_LOST | FIRST_LOST | NO_LOSER
    
    fun fight_result_toString r = case r of 
          SECOND_LOST => "SECOND_LOST"
        | FIRST_LOST => "FIRST_LOST"
        | NO_LOSER => "NO_LOSER"

    (* 
      A bout between contestants, such that (A beats B) and (B beats C) implies (A beats C);
      the loser is eliminated.
      If neither (A beats B) nor (B beats A), contestants can "both" win; then neither is eliminated.
      Returns the final "survivors" of up to n**2 pairwise matches.
    *)
    fun bout f contestants = case contestants of
                [] => []
              | c1 :: rest =>
                    let fun fight acc [] = SOME acc
                          | fight acc (c2 :: cs) =
                                let in case f (c1, c2) of
                                             SECOND_LOST => fight acc cs
                                           | FIRST_LOST =>   (* c1 lost to c2; eliminate c1 *)
                                                 NONE
                                           | NO_LOSER => fight (c2 :: acc) cs
                                end
                    in
                        case fight [] rest of 
                            NONE => bout f rest
                          | SOME rest' => c1 :: (bout f rest')
                    end




    fun reqSubtype failure (ctx as (rctx, mctx)) (A1, A2) kSucc =
        Subtype.subtypeLeft Context.NONFLEX failure (rctx, mctx) A1 A2
                  (fn (failure, (rctx(*???*), mctx'), coercion (*XXX*)) =>
                      kSucc (failure, (rctx, mctx')))

    fun reqSubtypeFlexing failure (ctx as (rctx, mctx)) (A1, A2) kSucc =
      let in
         dprint (fn () => "reqSubtypeFlexing: " ^ t2str A1 ^ " <=? " ^ t2str A2 ^ ":");
         Subtype.subtypeLeft Context.FLEX failure (rctx, mctx) A1 A2
                  (fn (failure, (rctx(*!!!*), mctx'), coercion (*XXX*)) =>
                      let in
                          dprint (fn () => "reqSubtypeFlexing. " ^ t2str A1 ^ " <= " ^ t2str A2 ^ " \"derived\"");
                          kSucc (failure, (rctx, mctx'))
                      end)
      end

    fun reqProp failure (ctx as (rctx, mctx)) P kSucc =
        Context.%%%% (failure) (mctx, Prop P)
        (fn mctx =>
        kSucc (failure, (rctx, mctx)))

    fun suppIndex (ctx as (rctx, mctx)) (exvars, assns) kSucc =
        let val mctx' = List.foldl (fn (x, mctx) => forceSingleton (mctx %% x)) mctx assns
            val mctx'' = List.foldl (fn (tv, mctx) => addExtype mctx tv) mctx' exvars
        in
            kSucc (rctx, mctx'')
        end


    fun collectCore mctx A acc prev_tuples (tuples : tuple list) k =
        case tuples of
            [] => k acc
          | (tuple as TUP{rctx= rctxHigh,
                          conjunct= conjunct, (* KEY POINT *)
                          things= (exvarsHigh, assnsHigh),
                          varmap= varmap,
                          constraint= WHigh,
                          domain= domOpt,
                          codomain= cod})
               ::
              rest
            =>
                let
                    val rctx = rctxHigh
                    val ctx = (rctx, mctx)
                in
                    (* 1. suppIndex adds index assumptions *)
                    suppIndex ctx (exvarsHigh, assnsHigh)
                         (fn (ctx as (rctx, mctxSilly)) =>
                               allSols mctxSilly (fn failure => fn kk =>
                                   (* reqProp adds WHigh *)
                                   reqProp failure ctx WHigh kk)
                               (fn results =>
                                   concatSolsAppliedToList
                                       []
                                       mctxSilly
                                       results
                                       (fn ctx => fn failure => fn kk => 
                                           reqSubtypeFlexing failure ctx (cod, A) kk)
                                       (fn results =>
                                           let val tupleizedResults =
                                                   List.map (fn ctx =>
                                                                     INTUP{previous= prev_tuples @ rest,
                                                                           ctx= ctx,
                                                                           conjunct= conjunct,
                                                                           varmap= varmap,
                                                                           domainOpt= domOpt,
                                                                           codomain= cod})
                                                            results
                                           in
                                               collectCore mctx A
                                                   (tupleizedResults @ acc)    (* Accumulate *)
                                                   (tuple :: prev_tuples)      (* Add to list of already-seen tuples  *)
                                                   rest
                                                   k
                                           end)))
                end

    fun tupleizedResultToString (INTUP{conjunct, previous= prev_tuples, ctx= (rctx, mctx), codomain= cod, domainOpt, ... }) =
        " (conjunct= " ^ PV.toString conjunct ^ ", " (*^ mctxToString mctx*)
         ^ ", domainOpt= " ^ (case domainOpt of NONE => "nullary" | SOME domain => t2str domain)
         ^ ", cod = " ^ t2str cod ^ ") "

    fun collect mctx A (tuples : tuple list) k =
            (* At this point, the tuples exclude constructor codomains that are impossible by reason of datasort refinements,
                but include codomains that are impossible by reason of index refinements. *)
            (dprint (fn () => "collect [] [] " ^ tuplesToString tuples);
             collectCore mctx A [] [] tuples
             (* Now, the tuples exclude constructor codomains that are impossible by reason of datasort refinements,
  AND codomains impossible by reason of index refinements. *)
                   (fn tupleizedResults =>
                       (
                       (*print ("Number of doubly weeded tuples: " ^ Int.toString (List.length tupleizedResults) ^ "\n");*)
                       dprint (fn () => "collect: returning:\n"
                                                               ^ Separate.list ",,,\n" (List.map tupleizedResultToString tupleizedResults));
                       k tupleizedResults)))




  
    fun toXi''  nilcase  (ctx, A, Cl, cod, lastmile_pat)  failure tups k =
        let
            fun toXi''_aux failure [] k = nilcase() (*raise_Dead failure mctxThisTuple (fn () => "build_pattern_tracks try exhausted")*)
              | toXi''_aux failure  (TUP{rctx= rctx,
                                     conjunct= conjunct,
                                     things= assns'',
                                     constraint= W'',
                                     varmap= varmap,
                                     domain= SOME dom'',
                                     codomain= cod''} :: rest) k =
                     let val k = k     (* fn (x as (_, cod, ctx)) => ( (*print ("======" ^ t2str cod ^ "\n"); *) k x) *)
                         fun kFail _ = toXi''_aux failure rest k
                         (* 666 *)
                         val TUP {rctx= rctx,
                                  conjunct= conjunct,
                                  things= assns'',
                                  constraint= W'',
                                  varmap= varmap,
                                  domain= SOME dom'',
                                  codomain= cod''}
                             =
                                 (* freshen *)
                                 TUP {rctx= rctx, conjunct= conjunct, things= assns'',
                                      varmap= varmap,
                                      constraint= W'',
                                      domain= SOME dom'', codomain= cod''}
                     in
                         suppIndex ctx assns''
                         (fn ctx =>
                             reqProp kFail ctx W''
                               (fn (failure, ctx) =>
                                   (  (* print  "last_mile.ff.toXi''_aux.reqSubtypeFlexing\n"; *)
                                      reqSubtypeFlexing failure ctx (cod'', A)
                                         (fn (failure, ctx) =>
                                             (
                                              reqSubtype failure ctx (Arrow(dom'', cod''), Arrow(Cl, cod))
                                                         (fn (failure, ctx) => 
                                                             (* reqSubtype failure ctx (Cl, dom) fn (failure, ctx) => *) (
                                                             (* reqSubtype failure ctx (dom'', dom) fn (failure, ctx) => *) (
                                                              let val failure = fn _ => toXi''_aux failure rest k
                                                              in
                                                                  k (failure, OTRK(SOME lastmile_pat (*???*), conjunct, varmap, (dom'', cod''), ctx))
                                                              end)
                                                              ))
                           )))))
                     end (* end of toXi''_aux, nonempty clause *)
        in
            toXi''_aux failure tups k
        end (* end of toXi'' *)




    fun ff 
            build_pattern_tracks
            (ctx as (rctx, mctx), pat0, fail, A)
            failure
            (INTUP{previous= otherTuples, conjunct= conjunct,
                   varmap,
                   ctx= ctxThisTuple, domainOpt= domOpt, codomain= cod})
            (kk : result failure * xi_track list -> result)
    =    
        let fun last_mile
                (A, dom, cod)
                failure
                (TRK (lastmile_pat, Cl, ctxThisTuple as (rctxThisTuple, mctxThisTuple)))     (* Member of Xi' *)
                (k : result failure * option_track -> result)
            =
                let val ctx = ctxThisTuple
                    val rctx = rctxThisTuple
                    val mctx = mctxThisTuple
                    fun nilcase() = raise_Dead failure mctxThisTuple (fn () => "build_pattern_tracks try exhausted")
                    fun kFail _ =
                              (* Ignore this TRK *)
                              toXi'' nilcase
                                     (ctx, A, Cl, cod, lastmile_pat)
                                     failure
                                     otherTuples
                                     k  
                in 
                    reqSubtype
                          kFail (* if Cl (domain from track) is not a subtype of dom, ignore this tuple *)
                          ctxThisTuple (Cl, dom)  (* morally (and precisely): (Arrow(dom, cod), Arrow(Cl, cod)) *)
                          (fn (failure, ctx) => 
                              (k (fn _ => toXi'' nilcase (ctx, A, Cl, cod, lastmile_pat) failure otherTuples k,
                                    OTRK(SOME lastmile_pat (*???*),
                                         conjunct,
                                         varmap,
                                         (dom, cod),
                                         ctx))))
                end (* fun last_mile *)

            val ctx = ctxThisTuple (* confusing as hell *)
            fun k (failure, xitrks) = kk (failure, List.map (fn XITRK(pattern, pv, A, ctx) => XITRK (pattern, pv, A, ctx)) xitrks)
        in
            case (domOpt, pat0) of
                (SOME dom, SOME pat0) =>
                        build_pattern_tracks failure (TRK (pat0, dom, ctxThisTuple))
                        (fn (failure, Xi') =>
                            let
                                fun build failure tracks [] k =
                                    k (failure, 
                                       List.map (fn OTRK(pat, pv, varmap, (dom, cod), ctx) =>
                                                    (dprint (fn () => "build: XITRK with pattern " ^ PV.toString pv ^ "  " ^ patternOptionToString pat ^ "; "
                                                                       ^ t2str dom ^ " -> " ^ t2str cod);
                                                     XITRK(pat, pv, cod, ctx)))
                                                tracks)

                                  | build failure tracks (part :: parts) k = 
                                       allSols mctx (fn failure => fn kk => last_mile (A, dom, cod) failure part kk)
                                             (* resultTracks: all solutions produced by last_mile *)
                                             (fn resultTracks : option_track list =>  
                                                 (*
                                                  Now I can choose any of these.
                                                  Choose the _smallest_.
                                      *)
        (*                                                       
                                 build failure (resultTracks @ tracks) parts k
        *)

                                                let 
                                                    val _ = dprint (fn () => "build; my resultTracks are: " ^ Context.otrksToString resultTracks ^ "\n>>>>>>>>>\n")
                                                    (* val _ = dprint (fn () => "****** build ::  " ^ Int.toString (List.length tracks) ^ " / " ^ Int.toString (List.length parts + 1) ^ "\n\n") *)
                                                    fun eqtrack (OTRK(_, ck1, _, (dom1, cod1), _), OTRK(_, ck2, _, (dom2, cod2), _)) =
                                                        (ck1 = ck2) andalso (dom1 = dom2) andalso (cod1 = cod2)
                                                    val keyed = MyList.elimDups' eqtrack resultTracks

                                                    exception Pointless

                                                    fun beats (OTRK(pat1, ck1, varmap1, key1, rec1),
                                                               OTRK(pat2, ck2, varmap2, key2, rec2)) =
                                                                          let
                                                                          in case (key1, key2) of
                                                                                     ((dom1, t1 (* as Tycon(tc1, i1, []) *)),
                                                                                      (dom2, t2 (* as Tycon(tc2, i2, []) *)  ))
                                                                                     =>
                                                                                         let 
                                                                                             val _ = dprint (fn () => "beats: " ^ t2str dom1 ^ " -> " ^ t2str t1 ^ " vs. " ^ t2str dom2 ^ " -> " ^ t2str t2)
                                                                                             
                                                                                             fun checkDS () = 
                                                                                                 if fastIncompleteSubtype dom1 dom2 andalso fastIncompleteSubtype t1 t2 then
                                                                                                     SECOND_LOST
                                                                                                 else if fastIncompleteSubtype dom2 dom1 andalso fastIncompleteSubtype t2 t1 then
                                                                                                     FIRST_LOST
                                                                                                 else
                                                                                                     NO_LOSER

                                                                                             val result = checkDS()
                                                                                         in
                                                                                             dprint (fn () => "beats: " ^ fight_result_toString result);
                                                                                             checkDS()
                                                                                         end

(*
                                                                                   | _ => 
                                                                                     let
                                                                                             val varmap1to2 = Renaming.compose (Renaming.inverse varmap2) varmap1
                                                                                             val _ = print ("VARMAP1to2: " ^ Renaming.toString varmap1to2 ^ "\n")
                                                                                             val subst1to2 = List.map (fn (a, b) => (a, X.Uvar b)) (Renaming.toList varmap1to2)
        (*                                                                                             val infons = List.map (fn (one, two) => InfoIndexSym (one, two)) (Renaming.toList varmap1) *)
                                                                                         in
                                                                                             case (i1, i2) of
                                                                                                 (Indexing.N, Indexing.N) => checkDS()
                                                                                               | (Indexing.O i1, Indexing.O i2) =>
                                                                                                     let 
                                                                                                         (* val _ = print ("i1 = " ^ X.Exp.toString i1 ^ "\n" ^ "i2 = " ^ X.Exp.toString i2 ^ "\n") *)
                                                                                                         val i1 = Indexing.subst subst1to2 i1
                                                                                                         (* val _ = print ("i1 = " ^ X.Exp.toString i1 ^ "\n" ^ "i2 = " ^ X.Exp.toString i2 ^ "\n") *)
                                                                                                     in
                                                                                                         case compose [] (Context.eq_texp_ignoring_datasorts (dom1, dom2)) (Context.eq_index (i1, i2)) of
                                                                                                             SOME renaming =>  (print "calling checkDS()\n"; checkDS())
                                                                                                           | NONE => (print "eq_texp_ign --> NONE; raising Pointless\n";
                                                                                                                      raise Pointless)
                                                                                                     end
                                                                                         end
*)
                                                                          end

                                                    val sortedTracks (*misnamed*) = 
                                                        bout beats keyed
                                                    
                                                    val origLength = List.length keyed
                                                    val _ = dprint (fn () => "origLength = " ^ Int.toString origLength)
                                                    val _ = dprint (fn () => "keyed = " ^ Context.otrksToString keyed)
                                                    val sortedLength = List.length sortedTracks
                                                    val _ = dprint (fn () => "sortedTracks = " ^ Context.otrksToString sortedTracks)
                                                    val _ = if sortedLength < origLength then
                                                                dprint (fn () => "  -" ^ Int.toString (origLength - sortedLength) ^ "  ")
                                                            else ()
                                                in
                                                    case sortedTracks of
                                                        [] => build failure ([] @ tracks) parts k
                                                      | [one] => build failure (one :: tracks) parts k
                                                      | several =>
                                                              let fun tryAll ultimateFailure f xs = case xs of
                                                                  [] => raise_Dead ultimateFailure mctx (fn () => "ctorPatternOrNondet $")
                                                                | x :: xs => (Counter.INC "ctorPatternOrNondet" ctorPatternOrNondet;
                                                                              f (fn _ => tryAll ultimateFailure f xs) x)
                                                              in
                                                                  tryAll
                                                                    failure
                                                                    (fn failure => fn track => build failure (track :: tracks) parts k)
                                                                    several
                                                              end
                                                end)
    (*                                 last_mile failure part
                             (fn (failure, track) => build failure (track :: tracks) parts k)     *)
                              in
                                  build failure [] Xi' k
                              end)

              | (NONE, NONE) =>
                     let val (rctx, mctx) = ctx
                     in
                         dprint (fn () => "ff: nullary constructor: " ^ mctxToString mctx ^ " |- " ^ t2str cod);
                         k (failure, [XITRK(NONE, conjunct, cod, ctx)])
                     end

              | (NONE, SOME _) => fail "Nullary constructor used as non-nullary pattern"
              | (SOME _, NONE) => fail "Non-nullary constructor used as nullary pattern"
          end (* body of `ff' *)

end (* structure Case *)