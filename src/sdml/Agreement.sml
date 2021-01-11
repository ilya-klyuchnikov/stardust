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
signature AGREEMENT = sig
  type fieldset = Indexing.fieldname list

  val fieldsOfIndexing : Indexing.record -> fieldset
  val fieldsOfType : Sdml.texp -> fieldset
  val fieldsOfTypes : Sdml.texp list -> fieldset
  val fieldsToString : fieldset -> string

  val agreesWith : Subtype.result Context.failure
                      -> Context.ctx
                      -> {oldType: Sdml.texp, oldSigFields: fieldset, typeToAdd: Sdml.texp}
                      -> (Subtype.result Context.failure * Context.ctx -> Subtype.result)
                      -> Subtype.result
end

structure Agreement :> AGREEMENT = struct
  val {dprint, dprnt} =
          Debug.register {full_name= "Agreement",
                          short_name= "Agreement"}

  local
      val index = Option.valOf (Debug.from "Agreement")
  in
      fun fail s =
          Debug.makeFail index s
  end

  open Sdml
  open Context
  infix 5 %%
  
  structure X = Indexing
  type fieldset = X.fieldname list

  structure CP = Print
  fun t2str texp = CP.pTexp texp

  fun fieldsOfIndexing r = case r of
      X.N => []
    | X.I defs => List.map #1 defs
    | X.O _ => []    (* ??? *)

  fun fieldsOfType A =
    let fun f A = case A of
          Typevar _ => []
        | Extypevar _ => []   (* ??? *)
        | All(_, _, A) => f A
        | Arrow(A1, A2) => f A1 @ f A2
        | Product As => List.concat (map f As)
        | Tycon(_, indexing, args) => List.concat (map f args) @ fieldsOfIndexing indexing
        | Sect(A1, A2) => f A1 @ f A2
        | Union(A1, A2) => f A1 @ f A2
        | Rsect(A1, A2) => f A1 @ f A2
        | Runion(A1, A2) => f A1 @ f A2
        | Univ(_, _, A) => f A
        | Exis(_, _, A) => f A
        | Top => []
        | Bot => []
        | Implies (_, A) => f A
        | Conj(_, A) => f A
  in
    MyList.elimDups (f A)
  end

  fun fieldsOfTypes As =
    MyList.elimDups (List.concat (List.map fieldsOfType As))
  val fieldsOfTypes = fieldsOfTypes : texp list -> X.fieldname list

  fun fieldsToString fieldnames = Separate.list ",   " (List.map (IndexFieldName.toShortString) fieldnames)

  fun agreesWith failure ctx {oldType, oldSigFields, typeToAdd} kSucc =
    let val _ = dprint (fn () => "agreesWith \n    oldType: " ^ t2str oldType ^ "\n    oldSigFields: " ^ fieldsToString oldSigFields ^ "\n    typeToAdd: " ^ t2str typeToAdd)
        fun varyR failure ctx typeToAdd kSucc = agreesWith failure ctx {oldType= oldType, oldSigFields= oldSigFields, typeToAdd= typeToAdd} kSucc

        fun agreesWithX failure (ctx as (rctx, mctx)) oldType typeToAdd kSucc =
       let val kSuccXXX = fn (failure, ctx, coercion(*XXX*)) => kSucc (failure, ctx)
           val _ = dprint (fn () => "agreesWithX: \n   oldType: " ^ t2str oldType ^ "\n   typeToAdd: " ^ t2str typeToAdd) in
       case (oldType, typeToAdd) of
           (Arrow(A1, A2),  Arrow(B1, B2)) =>
               Subtype.subtype failure 170555 ctx B1 A1 (fn (failure, ctx, coercion1(*XXX*)) =>
               Subtype.subtype failure 170556 ctx B2 A2 kSuccXXX)

         | (A as Tycon _,  B as Tycon _) =>
               Subtype.subtype failure 170557 ctx B A kSuccXXX
         
         | (Sect(A1, A2),  _) =>
               agreesWithX (fn _ => agreesWithX failure ctx A2 typeToAdd kSucc) ctx A1 typeToAdd kSucc

         | (Univ (aa, sort, AA),  _) =>
               let val a = IndexSym.new aa
                   val A = Types.substIndex [(aa, X.Evar a)] AA
                   val (rctx, mctx) = ctx
               in
                   agreesWithX failure (rctx, forceSingleton (mctx %% Iexists(a, sort))) A typeToAdd kSucc
               end

         | (Implies(P, A0),  _) => && failure (mctx, P) (fn mctx => agreesWithX failure (rctx, mctx) A0 typeToAdd kSucc)

         | _ => 
            fail ("Type " ^ t2str typeToAdd ^ " does not agree with former type " ^ t2str oldType)
       end
            
(*        val agreesWithX = agreesWithX : 'r failure -> ctx -> texp -> texp -> ('r failure * ctx -> 'r) -> 'r *)

        fun domain B =
          let val Bfields = fieldsOfType B
              val _ = dprint (fn () => "domain:         " ^ t2str B)
              val _ = dprint (fn () => "domain fields:  " ^ fieldsToString Bfields)
          in
              if MyList.disjoint Bfields oldSigFields then
                  kSucc (failure, ctx)
              else
                  agreesWithX failure ctx oldType typeToAdd kSucc
          end
    in 
      case typeToAdd of
       Sect(B1, B2) => varyR failure ctx B1 (fn (failure, ctx) => varyR failure ctx B2 kSucc)
     | Univ(bb, sort, BB) => let val b = IndexSym.new bb
                                               val B0 = Types.substIndex [(bb, X.Uvar b)] BB
                                          in
                                              varyR failure (applyMctx ctx op%% (Iall(b,sort))) B0 kSucc
                                          end

     | Implies(P, B0) => let val barrier_id = Barrier.new()
                                          val (rctx, mctx) = ctx
                                          val mctxP = forceSingleton (forceSingleton (mctx %% Barrier barrier_id) %% Prop P)
                                          val ctxP = (rctx, mctxP)
                                     in
                                         case getState mctxP of
                                           NONE => kSucc (failure, ctx)
                                         | SOME _ => varyR failure ctxP B0 kSucc
                                     end

     | Arrow(B1, B2) => domain B2
     | B2 as Tycon _ => domain B2
     | _ => agreesWithX failure ctx oldType typeToAdd kSucc
    end

(*
  val agreesWith = (agreesWith : unit failure -> ctx -> {oldType : texp, oldSigFields : X.fieldname list, typeToAdd : texp}
                                              -> (unit failure * ctx -> unit)
                                              -> unit)
*)
end
