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
signature SUBTYPE = sig

  type result = Sdml.locexp
  type coercion = Coercion.t

  val subtypeCalls : int ref
  val subtypeNRCalls : int ref
  val subtypeUnionSplits : int ref
  val subtypeMemoAdd : int ref
  val subtypeMemoHit : int ref

  val applyEquations : Context.mctx -> Sdml.texp -> Sdml.texp
 
  val subtype : result Context.failure
                  -> int
                  -> Context.ctx
                  -> Sdml.texp -> Sdml.texp
                  -> (result Context.failure * Context.ctx * coercion -> result)
                  -> result
  val ctxsubtype : result Context.failure
                     -> Context.ctx
                     -> (Sdml.concrete_ctxt * Sdml.texp)
                     -> (result Context.failure * Context.mctx * Sdml.texp -> result)
                     -> result

  val subtypeLeft : Context.flexibility
                      -> result Context.failure
                      -> Context.ctx
                      -> Sdml.texp -> Sdml.texp
                      -> (result Context.failure * Context.ctx * coercion -> result)
                      -> result

  val try_hints : result Context.failure
                    -> Context.ctx
                    -> Types.universe * Sdml.annotation
                    -> (result Context.failure * Context.mctx * Sdml.texp -> result)
                    -> result

end (* signature SUBTYPE *)


structure Subtype :> SUBTYPE = struct

  val {dprint, dprnt} =
          Debug.register {full_name= "Subtype",
                          short_name= "Subtype"}

  val subtypeCalls : int ref = ref 0
  val subtypeNRCalls : int ref = ref 0
  val subtypeUnionSplits : int ref = ref 0
  val subtypeMemoAdd : int ref = ref 0
  val subtypeMemoHit : int ref = ref 0

  open Sdml
  type result = locexp
  type coercion = Coercion.t
    

  open Context
  infix 5 %%
  infix 5 $+
  infix 5 ++
  infix 5 +-
  infix 5 +--+
  infix 5 +--+=
  infix 5 +~~+

  
  structure X = Indexing
  structure CP = Print
  structure CC = Sdml.ConcreteContext
  structure DS = Datasorts

  fun PRINT x = print x
  val INC = Counter.INC

  fun t2str texp = CP.pTexp texp
  val tv2str = TV.toString
  fun COVER loc = ()
  
  local
      val index = Option.valOf (Debug.from "Subtype")
  in
      fun fail s =
          Debug.makeFail index s
  end
  
  
(* XXX: duplicated in Typecheck.sml *)
  fun rlookup_tc fullctx info Empty tc' = fail ("rlookup_tc " ^ TC.toString tc' ^ " (" ^ info ^ ") " ^ rctxToString fullctx)
    | rlookup_tc fullctx info (Ctx(tc, what, ctx)) tc' =
        if tc=tc' then what else rlookup_tc fullctx info ctx tc'
  fun lookupTypeinfo rctx tc =
      rlookup_tc rctx ("") (getTypes rctx) tc
  fun lookupOrd info mctx pv =
      D.lookupOrdinary pv (getG mctx) ("Ord--"^info)
  fun lookupUnivType info mctx tv =
      D.lookupUnivType tv (getG mctx) ("Tyvars--"^info)
  fun getTyvar mctx tv = case lookupUnivType "" mctx tv of
     NONE => Typevar tv
   | SOME A => (print "~"; A)

(* applies type equations (substitution) in mctx to A *)
  fun applyEquations mctx A =
      SdmlFold.fold_texp
        (SdmlFold.texpSpec (fn A => case A of
                                                                      Typevar tvA =>
                                                                        let in (getTyvar mctx tvA)
                                                                         handle _ => A  (* Handle tyvar-not-found exception; this is a hack that avoids having to add typevars in quantifiers to mctx *)
                                                                        end
                                                                   | A => A))
        A

  and try_hints failure (rctx, mctx) (uu, hints) k =
      raise_Dead failure mctx (fn () => "try_hints")
(*
hints "temporarily" disabled (2013-02-25); SEE ALSO:  "ZZZHINTS" below
     let
       val _ = dprint (fn () => "try_hints: uu = " ^ Types.toString uu)
       fun contained (hintCtx, hintType) =
         let val _ = dprint (fn () => "contained: least_univ = " ^ Types.toString (Types.least_universe hintType))
         in
           Types.contains uu (Types.least_universe hintType) orelse Types.ground hintType
         end
     in
       case hints of
          [] => (dprnt "no hints"; raise_Dead failure mctx (fn () => "try_hints"))
        
        | (G0, A0) :: remaining_hints =>
              if not (contained(G0, A0)) then
                (dprint (fn () => "blocking hint " ^ t2str A0);
                 try_hints failure (rctx, mctx) (uu, remaining_hints) k)
              else
                 let val _ = dprint (fn () => "accepting hint " ^ t2str A0) in
                      ctxsubtype (fn _ => try_hints failure (rctx, mctx) (uu, remaining_hints) k)
                          (rctx, mctx) (G0, A0)
                          (fn (failure, mctx, A) => 
                             (dprint(fn () => "++  hint ::: " ^ t2str A ^ "\n" ^ ctxToString (rctx, mctx));
                              k (failure, mctx, A)))
                 end
     end
*)

 and subtypeLeft flexibility failure (rctx, mctx) A B kTakingRctx =
   let val kTakingRctx = fn (failure, (rctx, mctx), coercion) => (dprint (fn () =>
                                                              ">>>>left>>>> " ^ D.GammaToString (getG mctx) ^ " |--- " ^ t2str A ^ " <= " ^ t2str B ^ ".  VVV" ^ "\n"); kTakingRctx (failure, (rctx, mctx), coercion))
       val subtypeRight = subtype
       val subtype = ()  (* hide `subtype' so it can't be called by accident *)
       val subtypeLeft = subtypeLeft flexibility
       
       (* apply the existential substitution that is part of mctx *)
       val (mctx, A) = applyEx (mctx, A) (* XXX5 *)
       val (mctx, B) = applyEx (mctx, B) (* XXX5 *)
       
       val _ = dprint (fn () => "[[subtype  LEFT  "
                              ^ D.GammaToString (getG mctx)
                              ^ " |--- " ^ t2str A ^ "  <=  " ^ t2str B) 
       (* apply the substitution embodied in #tyvars(rctx) to A and B *)
       val A = applyEquations mctx A
       val B = applyEquations mctx B
       val A = Inject.clean A
       val B = Inject.clean B
(*
       val _ = print ("A after cleaning: " ^ t2str A ^ "\n")
       val _ = print ("B after cleaning: " ^ t2str B ^ "\n")
*)
       
       val _ = INC "subtypeCalls" subtypeCalls

       (* subtypeLeft *)       
       fun subtypeNI_L failure =
(* ZZZ *)
                     if A = B then kTakingRctx (failure, (rctx, mctx), Coercion.identity)
                     else

case (A, B) of
(* Rule (/\L1) *)
            (Sect(A1, A2), B) =>
                (COVER "subSectL1";
                 let val (A1, A2) = perm (A1, A2)
                     val failure = fn _ => subtypeNI_R failure

                     val kTakingRctx1 =
                         fn (failure, ctx, coercion1) => 
                            kTakingRctx (failure, ctx, Coercion.sectL1 coercion1)
                     val kTakingRctx2 =
                         fn (failure, ctx, coercion2) => 
                            kTakingRctx (failure, ctx, Coercion.sectL2 coercion2)
                 in
                    (subtypeLeft (fn _ => ((* Rule (/\L2) *)COVER "subSectL2";
                                       subtypeLeft failure (rctx, mctx) A2 B kTakingRctx2))
                             (rctx, mctx) A1 B kTakingRctx1)
                end)

          | (Rsect(A1, A2), B) =>
                (COVER "subSectL1";
                 let val (A1, A2) = perm (A1, A2)
                     val failure = fn _ => subtypeNI_R failure
                 in
                    (subtypeLeft (fn _ => ((* Rule (/\L2) *)COVER "subSectL2";
                                       subtypeLeft failure (rctx, mctx) A2 B kTakingRctx))
                             (rctx, mctx) A1 B kTakingRctx)
                end)

(* Rule (\Pi L) *)
          | (Univ(aa, sort, AA), B) =>
                (COVER "subPiL";
                 let val a = IndexSym.new aa
                    val A = Types.substIndex [(aa, X.Evar a)] AA
                    val failure = fn _ => subtypeNI_R failure
                in
                    subtypeLeft failure (rctx, forceSingleton (mctx %% Iexists(a, sort))) A B kTakingRctx
                end)

(* subtypeLeft *)
(* Rule (All L) *)
          | (All(aa, uu, AA), B) =>
                (COVER "AllL";
                 let val _ = dprint (fn () => "@@@@ All, _ <<<< " ^ t2str (All(aa, uu, AA)) ^ ",  " ^ t2str B)
                     val failure = fn _ =>
                                              (frameR mctx
                                                 (fn mctx =>
                                                    let val a = TV.new aa
                                                        val mctx = addExtype mctx a
                                                        val A = Types.substTypevar [(aa, Extypevar a)] AA
                                                        val _ = dprint (fn () => "AllL INST " ^ t2str AA ^ " ====> " ^ t2str A)
                                                        val failure = fn _ => (dprint (fn () => "@@@@ All, _ " ^ t2str (All(aa, uu, AA)) ^ ",  " ^ t2str B); subtypeNI_R failure)
                                                    in
                                                      subtypeLeft failure (rctx, mctx) A B
                                                    end)
                                                 kTakingRctx
                                              )
                 in
                     try_hints failure (rctx, mctx) (uu, (*D.getHints (getG mctx)*)[]     (*2013-02-25 ZZZHINTS; keep searching below AND in Typecheck.sml*))
                       (fn (failure, mctx, hintType) =>
                          let
                              val A = Types.substTypevar [(aa, hintType)] AA
(*                              val _ = print ("[Left Sub] INST " ^ t2str AA ^ " ====> " ^ t2str A ^ "\n")
                              val _ = print ("[Left Sub].............PROCEEDING WITH   " ^ CP.pTexp A ^ "\n") *)
                          in
                              subtypeLeft failure (rctx, mctx) A B kTakingRctx
                          end)
                 end)

(* subtypeLeft *)
(* Rule (\Sigma L) *)
          | (Exis(aa, sort, AA), B) =>
                (COVER "subSigmaL";
                 let val a = IndexSym.new aa
                    val A = Types.substIndex [(aa, X.Uvar a)] AA
                    val failure = fn _ => subtypeNI_R failure
                in
                    subtypeLeft failure (rctx, forceSingleton (mctx %% Iall(a, sort))) A B kTakingRctx
                end)

(* subtypeLeft *)
(* Rule (\conjty L) *)
           | (Conj(P, A), B) =>
(*                 subtypeLeft failure (rctx, mctx) A B kTakingRctx
YYY OK *)
               (COVER "subConjL";
                let val barrier_id = Barrier.new()
                    val mctxP = forceSingleton (forceSingleton (mctx %% Barrier barrier_id) %% Prop P)
                    val failure = fn _ => subtypeNI_R failure
                in
                    subtypeLeft failure (rctx, mctxP) A B
                    (fn (failure, (rctxP, mctxP), coercion) => quantifyUpToBarrier failure mctx mctxP barrier_id 
                                                                (fn mctx => kTakingRctx (failure, (rctxP(*???XXX*), mctx), coercion)))
                end)

(* subtypeLeft *)
(* Rule  (\impty L) *)
          (* This pattern match MUST follow the match for (\impty R) / (\conj L) !
           Otherwise reflexivity is not derivable:
           if trying to derive P imp A  <=  P imp A, if (\impty L) is tried,
               it will fail unless P happens to be provable under the existing context.
                   (Likewise with P conj A  <=  P conj A: (\conj R) fails.) *)
          | (Implies(P, A), B) =>
               (COVER "subImpL";
                let val failure = fn _ => subtypeNI_R failure
                in
                       %%%% failure (mctx, Prop P) (fn (mctx') => subtypeLeft failure (rctx, mctx') A B kTakingRctx)
                end)

          | _ => subtypeNI_R failure

(* subtypeLeft *)
      and subtypeNI_R failure = case (A, B) of
            (* Rule (\Pi R) *)
            (A, Univ(bb, sort, BB)) =>
                (COVER "subPiR";
                 let val b = IndexSym.new bb
                     val B = Types.substIndex [(bb, X.Uvar b)] BB
                     val failure = fn _ => subtypeNI_Z failure
                in
                    subtypeLeft failure (rctx, forceSingleton (mctx %% Iall(b, sort))) A B kTakingRctx
                end)

            (* Rule (All R) *)
          | (A, All(bb, uu, BB)) =>
                (COVER "AllR";
                 let val b = TV.new bb
                     val B = Types.substTypevar [(bb, Typevar b)] BB
                     val _ = dprint (fn () => "AllR INST " ^ t2str BB ^ " ====> " ^ t2str B)
                     val failure = fn _ => subtypeNI_Z failure
                in
                   frameR 
                     mctx
                     (fn mctx =>
                         (fn kTakingRctx => subtypeLeft failure (rctx, mctx +--+ (b, NONE)) A B kTakingRctx)
                     )
                     kTakingRctx
                end)

(* subtypeLeft *)
(* Rule (\Sigma R) *)
          | (A, Exis(bb, sort, BB)) =>
               (COVER "subSigmaR";
                let val b = IndexSym.new bb
                    val B = Types.substIndex [(bb, X.Evar b)] BB
                    val failure = fn _ => subtypeNI_Z failure
                in
                    subtypeLeft failure (rctx, forceSingleton (mctx %% Iexists(b, sort))) A B kTakingRctx
                end)

(* subtypeLeft *)
(* Rule (\/R1) *) (* subUnionR1 *)
          | (A, Union(B1, B2)) => 
                  let val kTakingRctx1 =
                             fn (failure, ctx, coercion1) => 
                                (COVER "subUnionR1";
                                 kTakingRctx (failure, ctx, Coercion.unionR1 coercion1))
                         val kTakingRctx2 =
                             fn (failure, ctx, coercion2) => 
                                (COVER "subUnionR2";
                                 kTakingRctx (failure, ctx, Coercion.unionR2 coercion2))

                         val failure1 = fn _ =>
                       (* Rule (\/R2) *)  (* subUnionR2 *)
                           let val _ = INC "subtypeUnionSplits" subtypeUnionSplits
                               val failureZ = fn _ => subtypeNI_Z failure
                           in
                               subtypeLeft failureZ (rctx, mctx) A B2 kTakingRctx1
                           end
                  in 
                      subtypeLeft failure1 (rctx, mctx) A B1 kTakingRctx2
                  end

(*subtypeLeft*)
          | (A, Runion(B1, B2)) => 
                  let
                         val failure1 = fn _ =>
                       (* Rule (\/R2) *)  (* subUnionR2 *)
                           let val _ = INC "subtypeUnionSplits" subtypeUnionSplits
                               val failureZ = fn _ => subtypeNI_Z failure
                           in
                               subtypeLeft failureZ (rctx, mctx) A B2 kTakingRctx
                           end
                  in 
                      subtypeLeft failure1 (rctx, mctx) A B1 kTakingRctx
                  end

(* subtypeLeft *)
          | (A, Implies(P, B)) =>
               (COVER "subImpR";
                let val barrier_id = Barrier.new()
                    val failure = fn _ => subtypeNI_Z failure
                    val mctxP = forceSingleton (forceSingleton (mctx %% Barrier barrier_id) %% Prop P)
                in
                    subtypeLeft failure (rctx, mctxP) A B
                    (fn (failure, (rctxP, mctxP), coercion) =>
                           quantifyUpToBarrier
                                 failure
                                 mctx
                                 mctxP
                                 barrier_id 
                                 (fn mctx => kTakingRctx (failure, (rctxP(*??XXX*), mctx), coercion)))
                end)

(* subtypeLeft *)
          | (A, Conj(P, B))  =>
(*                subtypeLeft failure (rctx, mctx) A B kTakingRctx
   YYY OK *)
                (COVER "subConjR";
                  let val failure = fn _ => subtypeNI_Z failure  in
                     (fn k => k (forceSingleton (mctx %% Prop P)))
                     (fn mctx =>
                          subtypeLeft failure (rctx, mctx) A B kTakingRctx)
                 end)

           | _ => subtypeNI_Z failure
      
(* subtypeLeft *)
      and subtypeNI_Z failure = raise_Dead failure mctx (fn () =>
                                                     "]]subtypeLeft  " ^ "  " ^  t2str A ^ "  **  " ^ t2str B)
 
      fun createTypeEqn failure (rctx, mctx) tv B k =
          let val mctxWithEqn = mctx +--+= (tv, SOME B)
          in
            k (failure, (rctx, mctxWithEqn), Coercion.identity (* XXX *))
          end

     fun infoSwitchTyvarOnLeft failure mctx message (tv, other) =
       if isUnionEx mctx tv then
          failure
       else
          case D.viable (getG mctx) tv other of
                false => failure
              | true => (fn _ => 
                                     kTakingRctx (failure, (rctx, solveExtype message mctx tv
                                                                              (fn UnknownEx => SolvedEx other
                                                                                | SectEx D => SectEx (Sect (D, other)))),  Coercion.identity (*XXX*) ))

     fun infoSwitchTyvarOnRight failure mctx message (other, tv) =
       if isSectEx mctx tv then
          failure
       else
          case D.viable (getG mctx) tv other of
                false => failure
              | true => (fn _ => 
                                     kTakingRctx (failure, (rctx, solveExtype message mctx tv
                                                                              (fn UnknownEx => SolvedEx other
                                                                                | UnionEx D => UnionEx (Union (D, other)))), Coercion.identity (* XXX *) ))
   in
(* subtypeLeft *)
        case (A, B) of

(* PART 1:   INVERTIBLE RULES *)

(* subtypeLeft *)
(* Rule (BotL) *)
            (Bot, _) => (COVER "subBotL"; kTakingRctx (failure, (rctx, mctx), Coercion.identity (* the identity coercion indeed takes all values of type Bot to values of type B *) ))

(* subtypeLeft *)
(* Rule (TopR) *)
          | (_, Top) => (COVER "subTopR"; kTakingRctx (failure, (rctx, mctx), Coercion.topR))

(* subtypeLeft *)
(* Invented rule (\Sigma LR) *)
          | (Exis(aa, sortA, AA), Exis(bb, sortB, BB)) =>
                (COVER "subSigmaL";
                 let val a = IndexSym.new aa
                    val A = Types.substIndex [(aa, X.Uvar a)] AA

                    val b = IndexSym.new bb
                    val B = Types.substIndex [(bb, X.Evar b)] BB

                    val failure = fn _ => subtypeNI_Z failure
                in
                    subtypeLeft failure (rctx, forceSingleton (forceSingleton (mctx %% Iall(a, sortA)) %% Iexists(b, sortB))) A B kTakingRctx
                end)

(* subtypeLeft *)
          | (Record (fld1, A), Record (fld2, B)) =>
               (COVER "sub-record (subtypeLeft)";
                let val failure = fn _ => subtypeNI_Z failure
                in 
                    if fld1 <> fld2 then 
                        raise_Dead failure mctx (fn () => "Record field mismatch: " ^ fld1 ^ " <> " ^ fld2)
                    else
                        subtypeLeft failure (rctx, mctx) A B
                                (fn (failure, (rctx, mctx), coercionAB) =>
                                    kTakingRctx (failure, (rctx, mctx), coercionAB))
                end)

(* subtypeLeft *)
          | (Product [], Product []) => 
                kTakingRctx (failure, (rctx, mctx), Coercion.identity)

(* subtypeLeft *)
(* Rule ( * ) *)
          | (Product As, Product Bs) =>
               (COVER "sub1,*";
                let val failure = fn _ => subtypeNI_Z failure
                    (* val _ = print (t2str (Product As) ^ ";;;;\n" ^ t2str (Product Bs) ^ "\n") *)
                in case (As, Bs) of 
                    ([A], [B]) =>
                       let in
                          (* print ("subtypeLeft Product/Product case, [A] [B] case\n"); *)
                          subtypeLeft failure (rctx, mctx) A B
                            (fn (failure, (rctx, mctx), coercionAB) =>
                                let in
                                    (* print ("[A] [B] case; A = " ^ t2str A ^ "; " ^ " B = " ^ t2str B ^ ";\n");
                                    print ("coercion: " ^ Coercion.toString (Coercion.last coercionAB) ^ "\n"); *)
                                    kTakingRctx (failure, (rctx, mctx), Coercion.last coercionAB)
                                end)
                       end

                  | (A::As, B::Bs) =>
                        let in
                          subtypeLeft failure (rctx, mctx) A B
                            (fn (failure, (rctx, mctx), coercionAB) =>
                                let in 
                                   (* print ("A::As B::Bs inside; continuing with " ^ t2str(Product As) ^ " <= " ^ t2str (Product Bs) ^ "\n"); *)
                                   subtypeLeft failure (rctx, mctx) (Product As) (Product Bs)
                                            (fn (failure, (rctx, mctx), coercionAsBs) =>
                                                let val coercion = Coercion.cons (coercionAB, coercionAsBs)
                                                in
                                                    kTakingRctx (failure, (rctx, mctx), coercion)
                                                end)
                                end)
                        end

                  | (_, _) =>   (* lengths don't match *) 
                        raise_Dead failure mctx (fn () => "subtype: *'s of different sizes")
                end)


(* subtypeLeft *)
          | (Product As, Extypevar exbeta) =>
               (COVER "subEx*R";
                let val failure = fn _ => subtypeNI_Z failure
                    val exbetas = map (fn _ => TV.fresh "articExProdR") As
                    val articulation = Product (map Extypevar exbetas)
                    val articulatedMctx = solveExtypeArtic mctx
                                                           exbeta
                                                           exbetas
                                                           (fn UnknownEx => UnionEx articulation
                                                              | UnionEx D => UnionEx (Union (D, articulation)))
                in
                    subtypeLeft failure (rctx, articulatedMctx) (Product As) (Extypevar exbeta) kTakingRctx
                end)

(* subtypeLeft *)
          | (Extypevar exalpha, Product Bs) =>
                (COVER "subEx*L";
                 let val failure = fn _ => subtypeNI_Z failure
                     val exalphas = map (fn _ => TV.fresh "articExProdL") Bs
                     val articulation = Product (map Extypevar exalphas)
                     val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            exalphas
                                                            (fn UnknownEx => SectEx articulation
                                                              | SectEx D => SectEx (Sect (D, articulation)))
                 in
                     subtypeLeft failure (rctx, articulatedMctx) (Extypevar exalpha) (Product Bs) kTakingRctx
                 end)

(* subtypeLeft *)
(* Rule (->) *)
          | (Arrow(dA, codA),  Arrow(dB, codB)) =>
                (COVER "sub->";
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                     subtypeLeft failure (rctx, mctx) dB dA
                         (fn (failure, (rctx, mctx), domCoercion) =>
                             subtypeLeft failure (rctx, mctx) codA codB
                               (fn (failure, (rctx, mctx), codCoercion) =>
                                   let val coercion = Coercion.arr (domCoercion, codCoercion)
                                   in
                                       kTakingRctx (failure, (rctx, mctx), coercion)
                                   end))
                 end)

(* subtypeLeft *)
          | (Arrow(A1, A2),  Extypevar exalpha) =>
                (COVER "subExArr";
                 let val failure = fn _ => subtypeNI_Z failure
                     val exalpha1 = TV.fresh "articArrL"
                     val exalpha2 = TV.fresh "articArrR"
                     val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            [exalpha1, exalpha2]
                                                            (fn UnknownEx => UnionEx (Arrow(Extypevar exalpha1, Extypevar exalpha2)))
                 in
                     subtypeLeft failure (rctx, articulatedMctx) (Arrow(A1, A2)) (Extypevar exalpha) kTakingRctx
                 end)

(* subtypeLeft *)
          | (Extypevar exalpha, Arrow(B1, B2)) =>
                (COVER "subExArr";
                 let val failure = fn _ => subtypeNI_Z failure
                     val exalpha1 = TV.fresh "articArrL"
                     val exalpha2 = TV.fresh "articArrR"
                     val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            [exalpha1, exalpha2]
                                                            (fn UnknownEx => SectEx (Arrow(Extypevar exalpha1, Extypevar exalpha2)))
                 in
                     subtypeLeft failure (rctx, articulatedMctx) (Extypevar exalpha) (Arrow(B1, B2)) kTakingRctx
                 end)

(* subtypeLeft *)
(* Rule ????? PPP *)
          | (Typevar tvA, Typevar tvB) =>
                 if tvA = tvB then
                     kTakingRctx (failure, (rctx, mctx), Coercion.identity)
                 else
                     let val _ = dprint (fn () => "(Typevar tvA, Typevar tvB)")
                     in
                         case flexibility of
                            FLEX => createTypeEqn failure (rctx, mctx) tvA (Typevar tvB) kTakingRctx
                         | NONFLEX =>
                             raise_Dead failure mctx (fn () => "subtype: distinct type variables: fail")
                     end

(* subtypeLeft *)
(* Rule ????? PPP *)
          | (Extypevar extvA, Extypevar extvB) =>
               if extvA = extvB then
                 kTakingRctx (failure, (rctx, mctx), Coercion.identity)
               else
                 let val (extvA', extvB') = D.order (getG mctx) extvA extvB
                     val flavor = if extvA = extvA' then (fn UnknownEx => SectEx (Extypevar extvA'))
                                                                   else (fn UnknownEx => UnionEx (Extypevar extvA'))
                 in
                   kTakingRctx (failure, (rctx, solveExtype "^a-Refl" mctx extvB' flavor), Coercion.identity)
                 end
          
(* subtypeLeft *)
(****
          | (Extypevar extvA, B) =>
(*                kTakingRctx (failure, (rctx, solveExtype mctx extvA B)) *)
              subtypeNI_R
                (infoSwitchTyvarOnLeft failure mctx "exalpha<=_" (extvA, B))
****)

          | (Extypevar extvA, B) =>
(*                kTakingRctx (failure, (rctx, solveExtype mctx extvA B)) *)

                    kTakingRctx (fn _ =>
                                              subtypeNI_R
                                                  (infoSwitchTyvarOnLeft failure mctx "exalpha<=_" (extvA, B)),
                                 (rctx,
                                  solveExtype "exalpha<=_(greedy)" mctx extvA (fn UnknownEx => SectEx B | SectEx D => SectEx(Sect (D, B)))),
                                  Coercion.identity (*XXX*))



(* subtypeLeft *)
          | (A as Tycon(tcA, optindexA, texpsA as _ :: _),  Extypevar extvB) =>
               let val exvars = List.map (fn _ => TV.fresh "artic") texpsA
                   val articulation = Tycon(tcA, optindexA, List.map Extypevar exvars)
                   val mctx = solveExtypeArtic mctx extvB exvars (fn UnknownEx => UnionEx articulation)
               in
                     subtypeLeft failure (rctx, mctx) A articulation kTakingRctx
               end

(* subtypeLeft *)
          | (A as All _,  Extypevar extvB) =>
             let (* val _ = print ("@@@@ _, EXTYPEVAR <<<< " ^ t2str A ^ ",  " ^ t2str (Extypevar extvB) ^ "\n") *)
             in
              subtypeNI_L let in case D.viable (getG mctx) extvB A of
                    false => failure
                  | true => (fn _ => 
                                      let (* val _ = print ("@@@@ _, EXTYPEVAR <--< " ^ t2str A ^ ",  " ^ t2str (Extypevar extvB) ^ "\n") *)
                      (*                  val failure = fn _ => (print("@@@@//// _, Extypevar" ^ t2str A ^ ",  " ^ t2str (Extypevar extvB) ^  "\n"); subtypeNI_L()) *)
                                      in
                                            kTakingRctx (failure, (rctx, solveExtype "All <= exbeta" mctx extvB (fn UnknownEx => SolvedEx A)), Coercion.identity (* XXX *) )
                                      end)
                  end
             end

(* subtypeLeft *)
          | (A,  Extypevar extvB) =>
               let in case D.viable (getG mctx) extvB A of
                 false => subtypeNI_Z failure
               | true =>
                    let (* val _ = dprint (fn () => "@@@@ _, Extypevar ++-- " ^ t2str A ^ ",  " ^ t2str (Extypevar extvB)) *)
                    in
                          kTakingRctx (failure, (rctx, solveExtype "A <= exbeta" mctx extvB (fn UnknownEx => UnionEx A)), Coercion.identity (* XXX *))
                    end
               end

(* subtypeLeft *)
(* Rule (d) *)
          | (lhs as Tycon (tc1, record1, texps1), Tycon (tc2, record2, texps2)) =>
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                     if tc1 = tc2 orelse DS.blitheSubsort(tc1, tc2) then
                                let val Typeinfo{indexsort= sorting,
                                                  parameters= parameters, ...}
                                         = lookupTypeinfo rctx (DS.blitheRefines tc1)

(* subtypeLeft *)
                                    fun checkIndex failure (rctx, mctx) k = 
                                      let datatype eq = Eq of X.sort * X.exp * X.exp
                                         fun doEqs pointed_list mctx = case pointed_list of
                                                  NONE => k (failure, (rctx, updateState mctx (fn _ => NONE)), Coercion.identity (* XXX *))
                                             | SOME [] => k (failure, (rctx, mctx), Coercion.identity (* XXX*) )
                                             | SOME ((Eq eq) :: rest) =>
                                                  let in
                                                      (* Add the equality as an assumption *)
                                                          %%%% (failure) (mctx, Prop (X.mkEQ eq)) (doEqs (SOME rest))
                                                  end

(* subtypeLeft *)
                                          fun doDefault i1 =
                                            let val X.Sorting.Nameless (sort, defaultIndex) = sorting   (* guaranteed by Sortcheck *)
                                            in
                                              case defaultIndex of
                                                 NONE => []
                                               | SOME default => [Eq(sort, i1, default)]
                                            end

(* subtypeLeft *)
                                          fun doDefaults fields =
                                            let val X.Sorting.Fields fieldspecs = sorting   (* guaranteed by Sortcheck *)
                                                fun doField (fieldname, exp) =
                                                  let val (sort, default) = Option.valOf (Assoc.getOpt fieldspecs fieldname) in
                                                    case default of
                                                      NONE => NONE
                                                   | SOME defaultIndex => SOME (Eq(sort, exp, defaultIndex))
                                                  end
                                            in
                                               List.mapPartial doField fields
                                            end

                                          (* Check that, for each field in fields2, the index of the respective field is either (a) present in field1 and equal,
                                                                                                                                                     or (b) is the same as the default for that field *)
(* subtypeLeft *)
                                          fun doFields fields1 fields2 =
                                            let val X.Sorting.Fields fieldspecs = sorting   (* guaranteed by Sortcheck *)
                                                fun doField (fieldname, exp2) =
                                                  let val (sort, default) = Option.valOf (Assoc.getOpt fieldspecs fieldname)
                                                  in
                                                      case (Assoc.getOpt fields1 fieldname,  default) of
                                                          (SOME exp1, _) =>
                                                             (dprint (fn()=> "doFields: Eq " ^ X.Exp.toString exp1 ^ " = " ^ X.Exp.toString exp2);
                                                              SOME (Eq(sort, exp1, exp2)))

                                                        | (NONE, NONE) => 
                                                                let in
                                                                        dprint (fn () => "subtype LEFT _: field \"" ^ IndexFieldName.toShortString fieldname ^ "\" not in left-hand type " ^ t2str lhs)
(*                                                                              ; raise_Dead failure mctx (fn () => "subtype: field \"" ^ IndexFieldName.toShortString fieldname ^ "\" not in left-hand type " ^ t2str lhs) *)
                                                                      ; NONE
                                                                end

                                                        | (NONE, SOME defaultIndex) => SOME (Eq(sort, exp2, defaultIndex))
                                                  end
                                            in
(* subtypeLeft *)
                                                  let fun zero list = case list of [] => SOME [] | NONE :: _ => NONE | SOME x :: rest =>  let in case zero rest of NONE => NONE | SOME rest => SOME (x :: rest) end
                                                      val result = zero (List.map doField fields2)
(*                                                      val _  = print ("doFields length = " ^ Int.toString (List.length result) ^ "\n") *)
                                                  in
                                                      result
                                                  end
                                            end
                                      in                                        
(* subtypeLeft *)
                                          doEqs (case (record1, record2) of
                                              (X.N, X.N) =>   (* No indices given; if there's a default, it's equal to itself, so succeed *)
                                                  SOME []

                                            | (X.O i1, X.N) =>    (* No index on RHS; check for a Nameless sorting, and make an equality with the 
                                                                        default index if necessary *)
                                                  SOME (doDefault i1)
                                            | (X.N, X.O i2) =>    (* symmetric to preceding case *)
                                                  SOME (doDefault i2)

                                            | (X.I fields, X.N) => SOME (doDefaults fields)
                                            | (X.N, X.I fields) => SOME (doDefaults fields)

                                            | (X.O i1, X.O i2) =>
                                                  let val X.Sorting.Nameless (sort, defaultIndex) = sorting   (* guaranteed by Sortcheck *)
                                                  in 
                                                    SOME [Eq(sort, i1, i2)]
                                                  end

                                            | (X.I fields1, X.I fields2) => ((*print "X.I _, X.I _\n"; *)doFields fields1 fields2)
 
                                            | (_, _) => 
                                                (raise_Dead failure mctx (fn () => "subtype: Tycon(_, NONE) not a subtype of Tycon(_, SOME) or vice versa")  (* Here it must be the case that tc1 <> tc2; otherwise Inject.sml would have prevented this situation *); raise Option)
                                          ) mctx
                                      end

(* subtypeLeft *)
                                    val (length1, length2, length3) = (List.length texps1, List.length parameters, List.length texps2)
                                    val _ = if length1 = length2 andalso length2 = length3 then ()
                                            else fail ("wrong number of parameters: should be " ^ Int.toString length2 ^", not " ^
                                                       Int.toString length1 ^ " and " ^ Int.toString length3)
                                    val triples = MyList.zip3 (texps1,
                                                               List.map (fn Tvinfo(_, variance) => variance) parameters,
                                                               texps2)
                                    (* e.g., triples =  [(A, Variance.Co, B),  (C, Variance.Contra, D)]
                                              yields obligations   A <= B   and   D <= C   *)

                                    fun checkParameters (rctx, mctx) [] = checkIndex failure (rctx, mctx) kTakingRctx
                                      | checkParameters (rctx, mctx) ((type1, variance, type2) :: rest) =
                                        let fun kk (failure, (rctx, mctx), coercion(*XXX*)) = checkParameters (rctx, mctx) rest
                                        in
                                            if type1 = type2 then kk (failure, (rctx, mctx), Coercion.identity)
                                            else case variance of 
                                                    Variance.Co =>         subtypeLeft failure (rctx, mctx) type1 type2 kk
                                                  | Variance.Contra => subtypeLeft failure (rctx, mctx) type2 type1 kk
                                                  | Variance.Non =>      subtypeLeft failure (rctx, mctx) type1 type2
                                                                                          (fn (failure, (rctx, mctx), coercion(*XXX*)) =>
                                                                                              subtypeLeft failure (rctx, mctx) type2 type1
                                                                                              kk)
                                        end
                                in checkParameters (rctx, mctx) triples end
                            else
                                raise_Dead failure mctx (fn () => "subtypeLeft: " ^ TC.toShortString tc1 ^ " </< " ^ TC.toShortString tc2)
                 end
                      
(* subtypeLeft *)
          (* Rule (/\R) *)
          | (A, Sect(B1, B2)) =>
                (COVER "subSectR";
                 let val (B1, B2) = perm (B1, B2)
                     val failure = fn _ => subtypeNI_L failure
                 in
                     subtypeLeft failure (rctx, mctx) A B1 (fn (failure, (rctx, mctx), coercion1) =>
                     subtypeLeft failure (rctx, mctx) A B2 (fn (failure, (rctx, mctx), coercion2) =>

                        kTakingRctx (failure, (rctx, mctx), Coercion.sectR (coercion1, coercion2))))
                 end)

(* subtypeLeft *)
          | (A, Rsect(B1, B2)) =>
                (COVER "subRsectR";
                 let val (B1, B2) = perm (B1, B2)
                     val failure = fn _ => subtypeNI_L failure
                 in
                     subtypeLeft failure (rctx, mctx) A B1 (fn (failure, (rctx, mctx), coercion1) =>
                     subtypeLeft failure (rctx, mctx) A B2 (fn (failure, (rctx, mctx), coercion2) =>
                     kTakingRctx (failure, (rctx, mctx), coercion1)))
                 end)

(* subtypeLeft *)
          (* Rule (\/L) *)
          | (Union(A1, A2), B) => 
                (COVER "subUnionL";
                 let val failure = fn _ => subtypeNI_R failure
                 in dprnt "\\/L";
                    subtypeLeft failure (rctx, mctx) A1 B (fn (failure, (rctx, mctx), coercion1) =>
                    subtypeLeft failure (rctx, mctx) A2 B (fn (failure, (rctx, mctx), coercion2) => 
                       kTakingRctx (failure, (rctx, mctx), Coercion.unionL (coercion1, coercion2))))
                 end)

(* subtypeLeft *)
          | (Runion(A1, A2), B) => 
                (COVER "subRunionL";
                 let val failure = fn _ => subtypeNI_R failure
                 in dprnt "\\/L";
                    subtypeLeft failure (rctx, mctx) A1 B (fn (failure, (rctx, mctx), coercion1) =>
                    subtypeLeft failure (rctx, mctx) A2 B (fn (failure, (rctx, mctx), coercion2) => 
                       kTakingRctx (failure, (rctx, mctx), coercion1)))
                 end)

(* subtypeLeft *)
          | (Typevar tvA, B) =>
                let val _ = dprint (fn () => "(Typevar tvA, B)")
                in case flexibility of
                  FLEX => createTypeEqn failure (rctx, mctx) tvA B kTakingRctx
                | _ => subtypeNI_L failure
                end

(* subtypeLeft *)
          | (A, Typevar tvB) => 
                let val _ = dprint (fn () => "(A, Typevar tvB)")
                in case flexibility of
                  FLEX => createTypeEqn failure (rctx, mctx) tvB A kTakingRctx
                | _ => subtypeNI_L failure
                end

(* subtypeLeft *)
(* END OF PART 1, INVERTIBLE RULES *)

          | (_, _) =>
                if 
                    A = B then kTakingRctx (failure, (rctx, mctx), Coercion.identity (* WRONG for Product; need Coercion.last. *) )
                else
                    subtypeNI_L failure
    end

  and subtype failure SRC (ctx as (rctx, mctx)) left right k =
        case (Context.noUnksType "subtype" mctx (Product[left,right]);
              (* !r_memoize *) NoMemo (* XXX *)) of
            NoMemo =>
              subtypeNoMemo failure SRC ctx left right
(*              (fn (failure2, mctx) =>
                  k (fn _ => k (failure2, mctx), mctx)
              )
*) k
          | _ => 
        let in (* case memoSubtype (ctx, left, right) (!universalHistoryOfInfamy) of
            NONE =>
*)
                let in
                    subtypeNoMemo failure SRC ctx left right
                    (fn (failure, (rctx', mctx'), coercion) =>
                     let in 
                         INC "subtypeMemoAdd" subtypeMemoAdd;
(*                         universalHistoryOfInfamy := MSubtype((ctx, left, right), SOME mctx') :: (!universalHistoryOfInfamy);
This is a pessimization.
Figures as of 2005-01-28:
 All tests except redblack:
    Without subtype memoization: wall 16s
    With subtype memoization: wall 19s
 redblack:
    Without subtype memoization: wall 13s
    With subtype memoization: wall 24s
*)
                         k (failure, (rctx', mctx'), coercion)
                     end)
                end
(*          | SOME info =>
                (INC "subtypeMemoHit" subtypeMemoHit;
(*                 print ("@@@memoHit\n"); *)
                 let in case info of
                     NONE =>
                         let (* val _ = print "memoized failure\n" *)
                         in
                             raise_Dead failure mctx (fn () => "memoized failure")
                         end
                   | SOME (mctx, info) => 
                         let (* val _ = print "memoized success\n" *)
                         in case !r_memoize of
                             SemiMemo => 
                                 subtypeNoMemo failure SRC ctx left right k
                           | FullMemo => 
                         let fun partition [] = ([], [])
                               | partition (infon :: rest) =
                                 let val (left, right) = partition rest
                                 in
                                     case infon of
                                         InfoIndexSym stuff => (stuff :: left, right)
                                       | InfoBarrierID stuff => (left, stuff :: right)
                                 end
                             val (newVarmap, barrierIDMap)  = partition info
                             val mctx = mapBarrierIDs mctx barrierIDMap
                             val mctx = compVarmap mctx (Renaming.fromList newVarmap)
                         in
                             k (failure, (rctx, mctx))
                         end
                         end
                 end)
*)
        end

(*    fun need b mctx k = if b then k mctx else raise_Dead failure mctx (fn () => "need")
*)

  and subtypeNoMemo (failure : result failure) SRC (rctx : rctx, mctx : mctx) A B (kTakingRctx : (result failure * (rctx * mctx) * coercion) -> result) =
  let (*val k = fn (failure, mctx) => kTakingRctx (failure, (rctx, mctx)) *)
       val _ = INC "subtypeNRCalls" subtypeNRCalls

      fun subtype failure (rctx, mctx) A B kTakingRctx =
   let val kTakingRctx = fn (failure, (rctx, mctx), result) => (dprint (fn () =>
                                                              ">>>> " ^ D.GammaToString (getG mctx) ^ " |--- " ^ t2str A ^ " <= " ^ t2str B ^ ".  VVV" ^ "\n"); kTakingRctx (failure, (rctx, mctx), result))

       fun elimSolvedEx C = case C of
          Extypevar tvC => (case getEx mctx tvC of SolvedEx sol => elimSolvedEx sol
                                                                          | _ => C)
        | C => C
       
       val A = elimSolvedEx A
       val B = elimSolvedEx B

       val _ = dprint (fn () => "SUBTYPE: " ^ Types.typeToString A ^ "  <=  " ^ Types.typeToString B)

      in
(*
              (Extypevar tvA, B) =>
                (case getEx mctx tvA of
                   SolvedEx solA => elimSolvedExes (solA, B)
                 | UnknownEx => process (A, B)
                 | _ => process (A, B))
*)
     let
(*       
       (* apply the existential substitution that is part of mctx *)
       val (mctx, A) = applyEx (mctx, A) (* XXX5 *)
       val (mctx', B) = applyEx (mctx, B) (* XXX5 *)
*)
       
       val _ = dprint (fn () => "[[subtype RIGHT "
                     ^ "  " ^ D.GammaToString (getG mctx) ^ " |--- " ^ t2str A ^ "  <=  " ^ t2str B) 
       (* apply the substitution embodied in #tyvars(rctx) to A and B *)
       val A = applyEquations mctx A
       val B = applyEquations mctx B
       val A = Inject.clean A
       val B = Inject.clean B
       val _ = dprint (fn () => "A after cleaning: " ^ t2str A ^ "\n")
       val _ = dprint (fn () => "B after cleaning: " ^ t2str B ^ "\n")

       val _ = INC "subtypeCalls" subtypeCalls
       
       fun subtypeNI_L failure = case (A, B) of
(* Rule (/\L1) *)
            (Sect(A1, A2), B) =>
                (COVER "subSectL1";
                 let val (A1, A2) = perm (A1, A2)
                     val failure = fn _ => subtypeNI_R failure

                     val kTakingRctx1 =
                         fn (failure, ctx, coercion1) => 
                            kTakingRctx (failure, ctx, Coercion.sectL1 coercion1)
                     val kTakingRctx2 =
                         fn (failure, ctx, coercion2) => 
                            kTakingRctx (failure, ctx, Coercion.sectL2 coercion2)
                 in
                    (subtype (fn _ => ((* Rule (/\L2) *)COVER "subSectL2";
                                       subtype failure (rctx, mctx) A2 B kTakingRctx2))
                             (rctx, mctx) A1 B kTakingRctx1)
                end)

          | (Rsect(A1, A2), B) =>
                (COVER "subSectL1";
                 let val (A1, A2) = perm (A1, A2)
                     val failure = fn _ => subtypeNI_R failure
                 in
                    (subtype (fn _ => ((* Rule (/\L2) *)COVER "subSectL2";
                                       subtype failure (rctx, mctx) A2 B kTakingRctx))
                             (rctx, mctx) A1 B kTakingRctx)
                end)

(* Rule (\Pi L) *)
          | (Univ(aa, sort, AA), B) =>
                (COVER "subPiL";
                 let val a = IndexSym.new aa
                    val A = Types.substIndex [(aa, X.Evar a)] AA
                    val failure = fn _ => subtypeNI_R failure
                in
                    subtype failure (rctx, forceSingleton (mctx %% Iexists(a, sort))) A B kTakingRctx
                end)

(* Rule (All L) *)
          | (All(aa, uu, AA), B) =>
                (COVER "AllL";
                 let val _ = dprint (fn () => "@@@@ All, _ <<<< " ^ t2str (All(aa, uu, AA)) ^ ",  " ^ t2str B)
                     val failure = fn _ =>
                                              (frameR mctx
                                                 (fn mctx =>
                                                    let val a = TV.new aa
                                                        val mctx = addExtype mctx a
                                                        val A = Types.substTypevar [(aa, Extypevar a)] AA
                                                        val _ = dprint (fn () => "AllL INST " ^ t2str AA ^ " ====> " ^ t2str A)
                                                        val failure = fn _ => (dprint (fn () => "@@@@ All, _ XXXX " ^ t2str (All(aa, uu, AA)) ^ ",  " ^ t2str B); subtypeNI_R failure)
                                                    in
                                                      subtype failure (rctx, mctx) A B
                                                    end)
                                                 kTakingRctx
                                              )
                 in
                     try_hints failure (rctx, mctx) (uu, (*D.getHints (getG mctx)*) []) (*ZZZHINTS*)
                       (fn (failure, mctx, hintType) =>
                          let
                              val A = Types.substTypevar [(aa, hintType)] AA
                              val _ = dprint (fn () => "[Left Sub] INST " ^ t2str AA ^ " ====> " ^ t2str A)
                              val _ = dprint (fn () => "[Left Sub] Continuing with " ^ CP.pTexp A)
                          in
                              subtype failure (rctx, mctx) A B kTakingRctx
                          end)
                 end)

(* Rule (\Sigma L) *)
          | (Exis(aa, sort, AA), B) =>
                (COVER "subSigmaL";
                 let val a = IndexSym.new aa
                    val A = Types.substIndex [(aa, X.Uvar a)] AA
                    val failure = fn _ => subtypeNI_R failure
                in
                    subtype failure (rctx, forceSingleton (mctx %% Iall(a, sort))) A B kTakingRctx
                end)

(* Rule (\conjty L) *)
           | (Conj(P, A), B) =>
(*                 subtype failure (rctx, mctx) A B kTakingRctx
YYY OK *)
               (COVER "subConjL";
                let val barrier_id = Barrier.new()
                    val mctxP = forceSingleton (forceSingleton (mctx %% Barrier barrier_id) %% Prop P)
                    val failure = fn _ => subtypeNI_R failure
                in
                    subtype failure (rctx, mctxP) A B
                    (fn (failure, (rctxP, mctxP), coercion) =>
                        quantifyUpToBarrier failure mctx mctxP barrier_id 
                                            (fn mctx => kTakingRctx (failure, (rctxP(*???XXX*), mctx), coercion(*XXX*))))
                end)

(* Rule  (\impty L) *)
          (* This pattern match MUST follow the match for (\impty R) / (\conj L) !
           Otherwise reflexivity is not derivable:
           if trying to derive P imp A  <=  P imp A, if (\impty L) is tried,
               it will fail unless P happens to be provable under the existing context.
                   (Likewise with P conj A  <=  P conj A: (\conj R) fails.) *)
          | (Implies(P, A), B) =>
               (COVER "subImpL";
                let val failure = fn _ => subtypeNI_R failure
                in
                    && failure (mctx, P) (fn (mctx') => subtype failure (rctx, mctx') A B kTakingRctx)
                end)

          | _ => subtypeNI_R failure

      and subtypeNI_R failure = case (A, B) of
            (* Rule (\Pi R) *)
            (A, Univ(bb, sort, BB)) =>
                (COVER "subPiR";
                 let val b = IndexSym.new bb
                     val B = Types.substIndex [(bb, X.Uvar b)] BB
                     val failure = fn _ => subtypeNI_Z failure
                in
                    subtype failure (rctx, forceSingleton (mctx %% Iall(b, sort))) A B kTakingRctx
                end)

            (* Rule (All R) *)
          | (A, All(bb, uu, BB)) =>
                (COVER "AllR";
                 let val b = TV.new bb
                     val B = Types.substTypevar [(bb, Typevar b)] BB
                     val _ = dprint (fn () => "AllR INST " ^ t2str BB ^ " ====> " ^ t2str B)
                     val failure = fn _ => subtypeNI_Z failure
                in
                   frameR 
                     mctx
                     (fn mctx =>
                         subtype failure (rctx, mctx +--+ (b, NONE)) A B
                     )
                     kTakingRctx
                end)

(* Rule (\Sigma R) *)
          | (A, Exis(bb, sort, BB)) =>
               (COVER "subSigmaR";
                let val b = IndexSym.new bb
                    val B = Types.substIndex [(bb, X.Evar b)] BB
                    val failure = fn _ => subtypeNI_Z failure
                in
                    subtype failure (rctx, forceSingleton (mctx %% Iexists(b, sort))) A B kTakingRctx
                end)

(* Rule (\/R1) *) (* subUnionR1 *)
          | (A, Union(B1, B2)) => 
                  let val kTakingRctx1 =
                             fn (failure, ctx, coercion1) => 
                                (COVER "subUnionR1";
                                 kTakingRctx (failure, ctx, Coercion.unionR1 coercion1))
                         val kTakingRctx2 =
                             fn (failure, ctx, coercion2) => 
                                (COVER "subUnionR2";
                                 kTakingRctx (failure, ctx, Coercion.unionR2 coercion2))

                         val failure1 = fn _ =>
                           (* Rule (\/R2) *) (* subUnionR2 *)
                               let val _ = INC "subtypeUnionSplits" subtypeUnionSplits
                                   val failureZ = fn _ => subtypeNI_Z failure
                               in
                                   subtype failureZ (rctx, mctx) A B2 kTakingRctx2
                               end
                  in 
                      subtype failure1 (rctx, mctx) A B1 kTakingRctx1
                  end

          | (A, Runion(B1, B2)) => 
                  let val failure1 = fn _ =>
                           (* Rule (\/R2) *) (* subUnionR2 *)
                               let val _ = INC "subtypeUnionSplits" subtypeUnionSplits
                                   val failureZ = fn _ => subtypeNI_Z failure
                               in
                                   subtype failureZ (rctx, mctx) A B2 kTakingRctx
                               end
                  in 
                      subtype failure1 (rctx, mctx) A B1 kTakingRctx
                  end

          | (A, Implies(P, B)) =>
               (COVER "subImpR";
                let val barrier_id = Barrier.new()
                    val failure = fn _ => subtypeNI_Z failure
                    val mctxP = forceSingleton (forceSingleton (mctx %% Barrier barrier_id) %% Prop P)
                in
                    subtype failure (rctx, mctxP) A B
                    (fn (failure, (rctxP, mctxP), coercion) => quantifyUpToBarrier failure mctx mctxP barrier_id 
                                                                (fn mctx => kTakingRctx (failure, (rctxP(*??XXX*), mctx), coercion)))
                end)

          | (A, Conj(P, B))  =>
(*                subtype failure (rctx, mctx) A B kTakingRctx
   YYY OK *)
                (COVER "subConjR";
                  let val failure = fn _ => subtypeNI_Z failure  in
                      && (failure) (mctx, P)
                      (fn mctx =>
                          subtype failure (rctx, mctx) A B kTakingRctx)
                 end)

           | _ => subtypeNI_Z failure
      
      and subtypeNI_Z failure = raise_Dead failure mctx (fn () =>
                                                     "]]subtype (right)  " ^  t2str A ^ "  **  " ^ t2str B)

(* 
      fun createTypeEqn failure (rctx, mctx) tv B k =
          let val mctxWithEqn = mctx +--+= (tv, SOME B)
          in
            k (failure, (rctx, mctxWithEqn))
          end
*)

     fun infoSwitchTyvarOnLeft failure mctx message (tv, other) =
       if isUnionEx mctx tv then
          failure
       else
          case D.viable (getG mctx) tv other of
                false => failure
              | true => (fn _ => 
                                     let val mctx = solveExtype message mctx tv
                                                                (fn UnknownEx => SolvedEx other
                                                                  | SectEx D => SectEx (Sect (D, other)))
                                     in
                                         kTakingRctx (failure, (rctx, mctx), Coercion.identity(*XXX*))
                                     end)

     fun infoSwitchTyvarOnRight failure mctx message (other, tv) =
       if isSectEx mctx tv then
          failure
       else
          case D.viable (getG mctx) tv other of
                false => failure
              | true => (fn _ => 
                                     let val mctx = solveExtype message mctx tv
                                                                (fn UnknownEx => SolvedEx other
                                                                  | UnionEx D => UnionEx (Union (D, other)))
                                     in
                                         kTakingRctx (failure, (rctx, mctx), Coercion.identity(*XXX*))
                                     end)


     fun theUsual failure = case (A, B) of
(* PART 1:   INVERTIBLE RULES *)

(* Rule (BotL) *)
            (Bot, _) => (COVER "subBotL"; kTakingRctx (failure, (rctx, mctx), Coercion.identity (* the identity coercion indeed takes all values of type Bot to values of type B *) ))

(* Rule (TopR) *)
          | (_, Top) => (COVER "subTopR"; kTakingRctx (failure, (rctx, mctx), Coercion.topR))

(* Invented rule (\Sigma LR) *)
          | (Exis(aa, sortA, AA), Exis(bb, sortB, BB)) =>
                (COVER "subSigmaL";
                 let val a = IndexSym.new aa
                    val A = Types.substIndex [(aa, X.Uvar a)] AA

                    val b = IndexSym.new bb
                    val B = Types.substIndex [(bb, X.Evar b)] BB

                    val failure = fn _ => subtypeNI_Z failure
                in
                    subtype failure (rctx, forceSingleton (forceSingleton (mctx %% Iall(a, sortA)) %% Iexists(b, sortB))) A B kTakingRctx
                end)

          | (Record (fld1, A), Record (fld2, B)) =>
               (COVER "sub-record";
                let val failure = fn _ => subtypeNI_Z failure
                in 
                    if fld1 <> fld2 then 
                        raise_Dead failure mctx (fn () => "Record field mismatch: " ^ fld1 ^ " <> " ^ fld2)
                    else
                        subtype failure (rctx, mctx) A B
                                (fn (failure, (rctx, mctx), coercionAB) =>
                                    kTakingRctx (failure, (rctx, mctx), coercionAB))
                end)

(* Rule ( * ) *)
(* Rule (1)     ---since Unit is represented by Product([]) *)
          | (Product As, Product Bs) =>
                 (COVER "sub1,*";
                  let val failure = fn _ => subtypeNI_Z failure
                  in case (As, Bs) of 
                      ([A], [B]) =>
                            subtype failure (rctx, mctx) A B
                              (fn (failure, (rctx, mctx), coercionAB) =>
                                  kTakingRctx (failure, (rctx, mctx), Coercion.last coercionAB))

                    | (A::As, B::Bs) =>
                            subtype failure (rctx, mctx) A B
                              (fn (failure, (rctx, mctx), coercionAB) =>
                                  subtype failure (rctx, mctx) (Product As) (Product Bs)
                                              (fn (failure, (rctx, mctx), coercionAsBs) =>
                                                  let val coercion = Coercion.cons (coercionAB, coercionAsBs)
                                                  in
                                                      kTakingRctx (failure, (rctx, mctx), coercion)
                                                  end))

                    | (_, _) =>   (* lengths don't match *) 
                              raise_Dead failure mctx (fn () => "subtype: *'s of different sizes")
                  end)

          | (Product As, Extypevar exbeta) =>
                 (COVER "subEx*R";
                  let val failure = fn _ => subtypeNI_Z failure
                  in
                    if isSectEx mctx exbeta then
                      raise_Dead failure mctx (fn () => "(Product _, exbetaSECT)")
                    else
                      let val exbetas = map (fn _ => TV.fresh "articExProdR") As
                          val articulation = Product (map Extypevar exbetas)
                          val articulatedMctx = solveExtypeArtic mctx
                                                                 exbeta
                                                                 exbetas
                                                                 (fn UnknownEx => UnionEx articulation
                                                                    | UnionEx D => UnionEx (Union (D, articulation)))
                      in
                        subtype failure (rctx, articulatedMctx) (Product As) articulation kTakingRctx
                      end
                  end)

          | (Extypevar exalpha, Product Bs) =>
                (COVER "subEx*L";
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                   if isUnionEx mctx exalpha then
                     raise_Dead failure mctx (fn () => "(exalphaUNION, Product _)")
                   else
                      let val exalphas = map (fn _ => TV.fresh "articExProdL") Bs
                          val articulation = Product (map Extypevar exalphas)
                          val articulatedMctx = solveExtypeArtic mctx
                                                                exalpha
                                                                exalphas
                                                                (fn UnknownEx => SectEx articulation
                                                                   | SectEx D => SectEx (Sect (D, articulation)))
                     in
                         subtype failure (rctx, articulatedMctx) articulation (Product Bs) kTakingRctx
                     end
                 end)

(* Rule (->) *)

          | (Arrow(dA, codA), Arrow(dB, codB)) =>
                (COVER "sub->";
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                     subtype failure (rctx, mctx) dB dA
                         (fn (failure, (rctx, mctx), domCoercion) =>
                             subtype failure (rctx, mctx) codA codB
                               (fn (failure, (rctx, mctx), codCoercion) =>
                                   let val coercion = Coercion.arr (domCoercion, codCoercion)
                                   in
                                       kTakingRctx (failure, (rctx, mctx), coercion)
                                   end))
                 end)

          | (Arrow(A1, A2), Extypevar exalpha) =>
                (COVER "subExArr";
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                   if isSectEx mctx exalpha then
                     raise_Dead failure mctx (fn () => "(Arrow _, exalphaSECT)")
                   else
                     let val exalpha1 = TV.fresh "articArrL"
                         val exalpha2 = TV.fresh "articArrR"
                         val arrow = Arrow(Extypevar exalpha1, Extypevar exalpha2)
                         val articulatedMctx = solveExtypeArtic mctx
                                                            exalpha
                                                            [exalpha1, exalpha2]
                                                            (fn UnknownEx => UnionEx arrow
                                                               | UnionEx D   => UnionEx (Union(D, arrow)))
                     in
                         subtype failure (rctx, articulatedMctx) (Arrow(A1, A2)) arrow kTakingRctx
                     end
                 end)

          | (Extypevar exalpha, Arrow(B1, B2)) =>
                (COVER "subExArr";
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                   if isUnionEx mctx exalpha then
                     raise_Dead failure mctx (fn () => "(exalphaUNION, Arrow _)")
                   else
                     let val exalpha1 = TV.fresh "articArrL"
                         val exalpha2 = TV.fresh "articArrR"
                         val arrow = Arrow(Extypevar exalpha1, Extypevar exalpha2)
                         val articulatedMctx = solveExtypeArtic mctx
                                                                exalpha
                                                                [exalpha1, exalpha2]
                                                                (fn UnknownEx => SectEx arrow
                                                                   | SectEx D => SectEx (Sect(D, arrow)))
                     in
                         subtype failure (rctx, articulatedMctx) arrow (Arrow(B1, B2)) kTakingRctx
                     end
                 end)

(* Rule ????? PPP *)
          | (Typevar tvA, Typevar tvB) =>
                 if tvA = tvB then
                     kTakingRctx (failure, (rctx, mctx), Coercion.identity)
                 else
                     let in
                          raise_Dead failure mctx (fn () => "subtype: distinct type variables: fail")
                     end

(* Rule ????? PPP *)
          | (Extypevar extvA, Extypevar extvB) =>
               if extvA = extvB then
                 kTakingRctx (failure, (rctx, mctx), Coercion.identity)
               else
                  let in case D.prec (getG mctx) extvA extvB of
                     LESS =>
                         (* extvA declared before extvB, so try to solve extvB := Extypevar extvA *)
                         (if isUnionEx mctx extvA then  (* no dice *)
                            raise_Dead failure mctx (fn () => "(ExtypevarUNION, Extypevar _)")
                          else
                            kTakingRctx (failure, (rctx,
                                                              solveExtype "^a-Refl" mctx extvB
                                                                                (fn UnknownEx => SectEx (Extypevar extvA)
                                                                                   | SectEx D => SectEx (Sect (D, Extypevar extvA)))),
                                         Coercion.identity (*XXX*)))
                  | GREATER =>
                         (* extvB declared before extvA, so try to solve extvA := Extypevar extvB *)
                         (if isSectEx mctx extvA then  (* no dice *)
                            raise_Dead failure mctx (fn () => "(Extypevar, ExtypevarSECT _)")
                          else
                            kTakingRctx (failure, (rctx,
                                                              solveExtype "^a-Refl" mctx extvA
                                                                                (fn UnknownEx => UnionEx (Extypevar extvB)
                                                                                   | UnionEx D => UnionEx (Union (D, Extypevar extvB)))),
                                          Coercion.identity (*XXX*)))
               end

          | (Extypevar extvA, B) =>
(*                kTakingRctx (failure, (rctx, solveExtype mctx extvA B)) *)

              let val failure =
                              fn _ =>
                                 subtypeNI_R (infoSwitchTyvarOnLeft failure mctx "exalpha<=_" (extvA, B))

                  val mctx = (SOME (solveExtype "exalpha<=_(greedy)" mctx extvA
                                                        (fn UnknownEx => SectEx B | SectEx D => SectEx(Sect (D, B)))))
                                      handle Match => NONE
              in
                  case mctx of
                      SOME mctx =>
                          kTakingRctx (failure, (rctx, mctx), Coercion.identity)
                    | NONE => failure()
              end
          

          | (A as Tycon(tcA, optindexA, texpsA as _ :: _),  Extypevar extvB) =>
               let val _ = dprint (fn () => "subtype Tycon(_,_,_::_) Extypevar")
                   val exvars = List.map (fn _ => TV.fresh "artic") texpsA
                   val articulation = Tycon(tcA, optindexA, List.map Extypevar exvars)
                   val mctx = solveExtypeArtic mctx extvB exvars (fn UnknownEx => UnionEx articulation
                                                                                              | UnionEx D => UnionEx (Union (D, articulation)))
               in
                  subtype failure (rctx, mctx) A articulation kTakingRctx
               end

          | (A as All _,  Extypevar extvB) =>
             let val _ = dprint (fn () => "@@@@ _, EXTYPEVAR <<<< " ^ t2str A ^ ",  " ^ t2str (Extypevar extvB))
             in
              subtypeNI_L (infoSwitchTyvarOnRight failure mctx "exalpha<=_" (A, extvB))
             end

          | (A,  Extypevar extvB) =>
               let val _ = dprint (fn () => "subtype " ^ t2str A ^" <= Extypevar " ^ tv2str extvB)
               in case D.viable (getG mctx) extvB A of
                 false => subtypeNI_Z failure
               | true =>
                    let val _ = dprint (fn () => "@@@@ _, Extypevar ++-- " ^ t2str A ^ ",  " ^ t2str (Extypevar extvB))
                        val mctx = 
                                 solveExtype "A <= exbeta" mctx extvB
                                        (fn UnknownEx => UnionEx A
                                          | UnionEx D => UnionEx (Union (D, A)))
                    in
                        kTakingRctx (failure, (rctx, mctx),
                                     Coercion.identity (*XXX*))
                    end
                    handle
                    Match => subtypeNI_Z failure
               end

(* Rule (d) *)
          | (lhs as Tycon (tc1, record1, texps1), Tycon (tc2, record2, texps2)) =>
                 let val failure = fn _ => subtypeNI_Z failure
                 in
                     if tc1 = tc2 orelse DS.blitheSubsort(tc1, tc2) then
                                let val Typeinfo{indexsort= sorting,
                                                  parameters= parameters, ...}
                                         = lookupTypeinfo rctx (DS.blitheRefines tc1)

                                    fun checkIndex failure (rctx, mctx) k = 
                                      let datatype eq = Eq of X.sort * X.exp * X.exp
                                         fun doEqs [] mctx = k (failure, (rctx, mctx), Coercion.identity(*XXX*))
                                           | doEqs ((Eq eq)::rest) mctx =
                                               let in    (* Add the equality as a constraint to be checked *)
                                                          && (failure) (mctx, X.mkEQ eq) (doEqs rest)
                                               end

                                          fun doDefault i1 =
                                            let val X.Sorting.Nameless (sort, defaultIndex) = sorting   (* guaranteed by Sortcheck *)
                                            in
                                              case defaultIndex of
                                                 NONE => []
                                               | SOME default => [Eq(sort, i1, default)]
                                            end

                                          fun doDefaults fields =
                                            let val X.Sorting.Fields fieldspecs = sorting   (* guaranteed by Sortcheck *)
                                                fun doField (fieldname, exp) =
                                                  let val (sort, default) = Option.valOf (Assoc.getOpt fieldspecs fieldname) in
                                                    case default of
                                                      NONE => NONE
                                                   | SOME defaultIndex => SOME (Eq(sort, exp, defaultIndex))
                                                  end
                                            in
                                               List.mapPartial doField fields
                                            end

                                          (* Check that, for each field in fields2, the index of the respective field is either (a) present in field1 and equal,
                                                                                                                                                     or (b) is the same as the default for that field *)
                                          fun doFields fields1 fields2 =
                                            let val X.Sorting.Fields fieldspecs = sorting   (* guaranteed by Sortcheck *)
                                                fun doField (fieldname, exp2) =
                                                  let val (sort, default) = Option.valOf (Assoc.getOpt fieldspecs fieldname)
                                                  in
                                                      case (Assoc.getOpt fields1 fieldname,  default) of
                                                          (SOME exp1, _) =>
                                                             (print ("doFields: Eq " ^ X.Exp.toString exp1 ^ " = " ^ X.Exp.toString exp2 ^ "\n");
                                                              SOME (Eq(sort, exp1, exp2)))

                                                        | (NONE, NONE) => 
                                                                              let in
                                                                                          (raise_Dead failure mctx
                                                                                                 (fn () => "subtype: field \"" ^ IndexFieldName.toShortString fieldname ^ "\" not in left-hand type " ^ t2str lhs); NONE)
                                                                              end

                                                        | (NONE, SOME defaultIndex) => SOME (Eq(sort, exp2, defaultIndex))
                                                  end
                                            in
                                                  let val result = List.mapPartial doField fields2
                                                      val _  = dprint (fn () => "doFields length = " ^ Int.toString (List.length result))
                                                  in
                                                      result
                                                  end
                                            end
                                      in                                        
                                          doEqs (case (record1, record2) of
                                              (X.N, X.N) =>   (* No indices given; if there's a default, it's equal to itself, so succeed *)
                                                  []

                                            | (X.O i1, X.N) =>    (* No index on RHS; check for a Nameless sorting, and make an equality with the 
                                                                        default index if necessary *)
                                                  doDefault i1
                                            | (X.N, X.O i2) =>    (* symmetric to preceding case *)
                                                  doDefault i2

                                            | (X.I fields, X.N) => doDefaults fields
                                            | (X.N, X.I fields) => doDefaults fields

                                            | (X.O i1, X.O i2) =>
                                                  let val X.Sorting.Nameless (sort, defaultIndex) = sorting   (* guaranteed by Sortcheck *)
                                                  in 
                                                    [Eq(sort, i1, i2)]
                                                  end

                                            | (X.I fields1, X.I fields2) => (print "X.I _, X.I _\n"; doFields fields1 fields2)
 
                                            | (_, _) => 
                                                (raise_Dead failure mctx (fn () => "subtype: Tycon(_, NONE) not a subtype of Tycon(_, SOME) or vice versa")  (* Here it must be the case that tc1 <> tc2; otherwise Inject.sml would have prevented this situation *); raise Option)
                                          ) mctx
                                      end

                                    val (length1, length2, length3) = (List.length texps1, List.length parameters, List.length texps2)
                                    val _ = if length1 = length2 andalso length2 = length3 then ()
                                            else fail ("wrong number of parameters: should be " ^ Int.toString length2 ^", not " ^
                                                       Int.toString length1 ^ " and " ^ Int.toString length3)
                                    val triples = MyList.zip3 (texps1,
                                                               map (fn Tvinfo(_, variance) => variance) parameters,
                                                               texps2)
                                    (* e.g., triples =  [(A, Variance.Co, B),  (C, Variance.Contra, D)]
                                              yields obligations   A <= B   and   D <= C   *)

                                    fun checkParameters (rctx, mctx) [] = checkIndex failure (rctx, mctx) kTakingRctx
                                      | checkParameters (rctx, mctx) ((type1, variance, type2) :: rest) =
                                        let fun kk (failure, (rctx, mctx), coercion(*XXX*)) = checkParameters (rctx, mctx) rest
(*                                            val _ = print "VARIANCECOPTER: \n"
                                            val _ = print (mctxToString mctx ^ "\n")
                                            val _ = print ("type1 = " ^ t2str type1 ^ " . " ^ Variance.toString variance ^ " . " ^ t2str type2 ^ " =  type2" ^ "\n")
*)
                                        in
                                            if type1 = type2 then kk (failure, (rctx, mctx), Coercion.identity(*XXX*))
                                            else case variance of 
                                                    Variance.Co =>         subtype failure (rctx, mctx) type1 type2 kk
                                                  | Variance.Contra => subtype failure (rctx, mctx) type2 type1 kk
                                                  | Variance.Non =>      subtype failure (rctx, mctx) type1 type2
                                                                                          (fn (failure, (rctx, mctx), coercion(*XXX*)) =>
                                                                                              subtype failure (rctx, mctx) type2 type1
                                                                                              kk)
                                        end
                                in checkParameters (rctx, mctx) triples end
                            else
                                raise_Dead failure mctx (fn () => "subtype: " ^ TC.toShortString tc1 ^ " </< " ^ TC.toShortString tc2)
                 end
                      
          (* Rule (/\R) *)
          | (A, Sect(B1, B2)) =>
                (COVER "subSectR";
                 let val (B1, B2) = perm (B1, B2)
                     val failure = fn _ => subtypeNI_L failure
                 in
                     subtype failure (rctx, mctx) A B1 (fn (failure, (rctx, mctx), coercion1) =>
                     subtype failure (rctx, mctx) A B2 (fn (failure, (rctx, mctx), coercion2) =>
                        kTakingRctx (failure, (rctx, mctx), Coercion.sectR (coercion1, coercion2))))
                 end)

          | (A, Rsect(B1, B2)) =>
                (COVER "subSectR";
                 let val (B1, B2) = perm (B1, B2)
                     val failure = fn _ => subtypeNI_L failure
                 in
                     subtype failure (rctx, mctx) A B1 (fn (failure, (rctx, mctx), coercion1) =>
                     subtype failure (rctx, mctx) A B2 (fn (failure, (rctx, mctx), coercion2) =>
                        kTakingRctx (failure, (rctx, mctx), coercion1)))
                 end)

          (* Rule (\/L) *)
          | (Union(A1, A2), B) => 
                (COVER "subUnionL";
                 let val failure = fn _ => subtypeNI_R failure
                 in dprnt "\\/L";
                    subtype failure (rctx, mctx) A1 B (fn (failure, (rctx, mctx), coercion1) =>
                    subtype failure (rctx, mctx) A2 B (fn (failure, (rctx, mctx), coercion2) => 
                       kTakingRctx (failure, (rctx, mctx), Coercion.unionL (coercion1, coercion2))))
                 end)

          | (Runion(A1, A2), B) => 
                (COVER "subUnionL";
                 let val failure = fn _ => subtypeNI_R failure
                 in dprnt "\\/L";
                    subtype failure (rctx, mctx) A1 B (fn (failure, (rctx, mctx), coercion1) =>
                    subtype failure (rctx, mctx) A2 B (fn (failure, (rctx, mctx), coercion2) => 
                       kTakingRctx (failure, (rctx, mctx), coercion1)))
                 end)

(* END OF PART 1, INVERTIBLE RULES *)

          | (_, _) => subtypeNI_L failure

   in
(* ZZZ *)
                     if A = B then kTakingRctx (failure, (rctx, mctx), Coercion.identity)
                     else

        theUsual (fn _ =>
                     if A = B then kTakingRctx (failure, (rctx, mctx), Coercion.identity)
                     else
                    case (A, B) of
                       (Extypevar tvA, Extypevar tvB) =>
                           let in case (D.prec (getG mctx) tvA tvB, getEx mctx tvA, getEx mctx tvB) of
                               (LESS, _, UnknownEx) =>
                                   kTakingRctx (failure, (rctx, unionEx mctx tvB (Extypevar tvA)), Coercion.identity(*XXX*))
                            | (LESS, _, UnionEx _) =>
                                   kTakingRctx (failure, (rctx, unionEx mctx tvB (Extypevar tvA)), Coercion.identity(*XXX*))
                            | (LESS, _, SectEx solB) =>
                                     subtype failure (rctx, updateG mctx (fn G => #1 (substExtypevarAuto' G B))) A solB kTakingRctx

                            | (GREATER, UnknownEx, _) =>
                                   kTakingRctx (failure, (rctx, sectEx mctx tvA (Extypevar tvB)), Coercion.identity(*XXX*))
                            | (GREATER, SectEx _, _) =>
                                   kTakingRctx (failure, (rctx, sectEx mctx tvA (Extypevar tvB)), Coercion.identity(*XXX*))
                            | (GREATER, UnionEx solA, _) =>
                                     subtype failure (rctx, updateG mctx (fn G => #1 (substExtypevarAuto' G A))) solA B kTakingRctx

                            | (_, SolvedEx _, _) => raise Option
                            | (_, _, SolvedEx _) => raise Option
                           end

                     | (A, Extypevar tvB) =>
                           let in case getEx mctx tvB of
                              SolvedEx _ => raise Option
                            | UnknownEx => raise_Dead failure mctx (fn () => "UnkEx")
                            | UnionEx solB =>
                                 if D.viable (getG mctx) tvB A then
                                     kTakingRctx (failure, (rctx, unionEx mctx tvB A), Coercion.identity(*XXX*))
                                 else
                                     (* SUBSTITUTE, CLOSING *)
                                     subtype failure (rctx, updateG mctx (fn G => #1 (substExtypevarAuto' G B))) A solB kTakingRctx
                             | SectEx solB =>
                                     (* SUBSTITUTE, CLOSING *)
                                      subtype failure (rctx, updateG mctx (fn G => #1 (substExtypevarAuto' G B))) A solB kTakingRctx
                           end

                     | (Extypevar tvA, B) =>
                           let in case getEx mctx tvA of
                              SolvedEx _ => raise Option
                            | UnknownEx => raise_Dead failure mctx (fn () => "UnkEx")
                            | SectEx solA =>
                                 if D.viable (getG mctx) tvA B then
                                     kTakingRctx (failure, (rctx, sectEx mctx tvA B), Coercion.identity(*XXX*))
                                 else
                                     (* SUBSTITUTE, CLOSING *)
                                     subtype failure (rctx, updateG mctx (fn G => #1 (substExtypevarAuto' G A))) solA B kTakingRctx
                             | UnionEx solA =>
                                     (* SUBSTITUTE, CLOSING *)
                                     subtype failure (rctx, updateG mctx (fn G => #1 (substExtypevarAuto' G A))) solA B kTakingRctx
                           end

                     | (_, _) => raise_Dead failure mctx (fn () => "Ex fallthru")
            )
(* Rule  (\impty R) *)  (* Rule  (\conj L) *)
          (* This pattern match MUST precede the match for (\impty R) / (\conj L) -- see below. *)
      (* XXX   NEED TO PROVE THAT THESE TWO RULES ARE INVERTIBLE!
       If they turn out to not be invertible, will need to add backtracking. *)
   (* In fact, I should "turn the tables" and convert the pattern sequence here
    into a formal system, then prove reflexivity, transitivity, and equivalence to
    the declarative system.  Doing so would have caught an obscure bug. *)
   end
   end
  in
      subtype failure (rctx, mctx) A B kTakingRctx
  end

  and ctxsubtype failure (rctx, mctx) ([], A0) k = k (failure, mctx, A0)
      | ctxsubtype failure (rctx, mctx) (ccelem :: cc, A0) k =
                let val _ = dprnt "ctxsubtype"
                in case ccelem of
                    CC.IndexVar(bb, sort) => 
                        let val b = IndexSym.new bb
                            val s = [(bb, X.Evar b)]
                            val cc' = CC.substIndex s cc
                            val mctx' = forceSingleton (mctx %% Iexists(b, sort))
                        in
                            ctxsubtype failure (rctx, mctx') (cc', Types.substIndex s A0) k
                        end

                  | CC.ProgramVar(pv, B) =>
                      let in case lookupOrd "ctxsubtype" mctx pv of
                                 (pv_texp, _) =>
                                     subtype failure 0 (rctx, mctx) pv_texp B
                                             (fn (failure, (_(*XXX*), mctx), coercion(*XXX*)) => ctxsubtype failure (rctx, mctx) (cc, A0) k)
                      end

                  | CC.TypeVar bb =>
                        let val b = TV.new bb
                            val s = [(bb, Extypevar b)]
                            val cc' = CC.substTypevar s cc
                            val mctx' = addExtype mctx b
                            val A0' = Types.substTypevar s A0
                            val _ = dprint (fn () => "ctxsubtype INST " ^ CP.pTyping (cc,A0) ^ " ====> " ^ CP.pTyping(cc', A0'))
                        in
                            ctxsubtype failure (rctx, mctx') (cc', A0') k
                        end
                end


(*****
(* "clean" types (Inject.clean *)
   val subtypeUnclean = subtype
   fun subtype failure n ctx A B k =
       subtypeUnclean failure n ctx (Inject.clean A) (Inject.clean B) k

   val ctxsubtypeUnclean = ctxsubtype
   fun ctxsubtype failure ctx (concrete_ctxt, A) k =
       ctxsubtypeUnclean failure ctx (concrete_ctxt, Inject.clean A) k

   val subtypeLeftUnclean = subtypeLeft
   fun subtypeLeft flexibility failure ctx A B k =
       subtypeLeftUnclean flexibility failure ctx (Inject.clean A) (Inject.clean B) k
*****)

end (* structure Subtype *)
