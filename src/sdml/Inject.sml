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
(* File: Inject.sml
   Author: Joshua Dunfield
   Contents: Code transformation: Injects types in annotations
     into the refined type system, and performs add'l simplifications:

inject_types
      - Replace each Tycon(tc, NONE, tvs) such that `tc' is a refined type
         with  Exis(a, sort, Tycon(tc, SOME (X.Evar a))) and `sort' refines `tc'.
      - ...unless there was a default index declaration with the type, e.g.
 
            primitive type real with dim = NODIM

flatten_productsort_quantifiers
      - Splay -all/exists a : sort- where `sort' is an n-ary product sort into
            -all/exists a1 : sort1, a2 : sort2, ..., a_n : sort_n-, and substitute
            (a1, ..., a_n) for `a' throughout the scope of `a'.

eliminate_subset_sorts
      - Replace subset sorts -all a : {a:sort | P} A with  -all a : sort- {P} A
         and -exists a : {a:sort | P} A with -exists a : sort- [P] A.

   History: 2004-06-23 [jcd] -- Created.
            2004-08-06 [jcd] -- Added eliminate_subset_sorts.
            2005-04-17 [jcd] -- Added flatten_productsort_quantifiers.
*)

signature INJECT = sig

  val clean : Sdml.texp -> Sdml.texp   (* = transform_quantifiers *)
  
  val transform_quantifiers : Sdml.texp -> Sdml.texp   (* like `eliminate_subset_sorts' *)
  
  val inject_type : (Sdml.tc -> Indexing.Sorting.t option) -> Sdml.texp -> Sdml.texp
  val inject_dectype : (Sdml.tc -> Indexing.Sorting.t option) -> Sdml.Dectype.dectype -> Sdml.Dectype.dectype
  
  val inject_types : Sdml.program -> Sdml.program
  val flatten_productsort_quantifiers : Sdml.program -> Sdml.program
  val eliminate_subset_sorts : Sdml.program -> Sdml.program

end (* signature INJECT *)


structure Inject :> INJECT = struct

  open Sdml

  structure P = Print
  structure X = Indexing

  val {dprint, dprnt} =
          Debug.register {full_name= "Inject",
                          short_name= "Inject"}
  val pprint = Debug.pprint

  fun updateSorting f (Datatype {tc, builtin, params, sorting, constructors}) =
      Datatype {tc= tc,
                builtin= builtin,
                params= params,
                sorting= f sorting,
                constructors= constructors}


  fun getTcAssoc (primtcs, typedecsl) =
      let val tcAssocFromLibinfo = primtcs

          fun extract (Datatype{tc, sorting, ...}) = (tc, sorting)
            | extract (Synonym{tc, tv, params, definition}) = (tc, X.Sorting.None) (* XXX *)

          val tcAssocFromAlgs = List.map extract (List.concat typedecsl)
          val tcAssoc : (tc * X.Sorting.t) list = tcAssocFromLibinfo @ tcAssocFromAlgs
      in
          tcAssoc
      end

  fun flatten (quant, corrVar) (tupleName, sorts, A) =
                let val components = MyList.mapWithCount 1 (fn (n, sort) => (IndexSym.fresh (IndexSym.toShortString tupleName ^ Int.toString n), sort)) sorts
                    val tuple = X.Tuple (map (corrVar o #1) components)
                    val A = Types.substIndex [(tupleName, tuple)] A
                    val result = List.foldr (fn ((name, sort), A) =>
                                                  case sort of
                                                      X.Product sorts => flatten (quant, corrVar) (name, sorts, A)
                                                    | _ => quant(name, sort, A))
                                            A
                                            components
                in
                    result
                end

  fun transform_quantifiers texp =
       case texp of
           Univ(a, X.Product sorts, A) => flatten (Univ, X.Uvar) (a, sorts, A)
         | Exis(a, X.Product sorts, A) => flatten (Exis, X.Evar) (a, sorts, A)
         | texp => texp

  (* val flatten_foldspec = SdmlFold.texpSpec transform_quantifiers *)
  
  fun inject_type get texp =
      let
          fun g (sort, i, texp) =
              case sort of
                  X.Subset(sort, a, P) =>
                      let val Psubstituted = X.Constraint.subst [(a, i)] P
                      in
                          Conj (Psubstituted, texp)
                      end
                | X.Product (sort1 :: sorts)  =>
                      let in case i of
                                 X.Tuple (i1 :: i's) => 
                                   g (X.Product sorts, X.Tuple i's, g (sort1, i1, texp))
                               | _ => g (X.Product sorts, i, g (sort1, i, texp))
                      end
                | sort => texp

          fun transform A =
              case A of
                  Tycon(tc, record, params) =>
                      let in case (get tc, record) of
                            (NONE, _) => (dprint (fn () => "inject: type " ^ TC.toString tc ^ "  not known");
                                                 A)
                          | (SOME X.Sorting.None, X.N) => A
                          | (SOME X.Sorting.None, record) => (pprint (fn () => "Inject: unindexed type " ^ TC.toString tc
                                                                          ^ " used with index ``" ^ Print.p Print.printIndexRecord record ^ "''");
                                                              raise Option)
                          | (SOME (X.Sorting.Nameless (sort, NONE)), X.N) => (* Type is indexed with no default index:  Add existential quantifier *)
                                  let val ex = IndexSym.fresh "ex"
(*                                      val _ = print ("inject: type " ^ TC.toString tc ^ "  is refined, adding Exis\n")
                                      val _ = print ("...its sort is " ^ X.Sort.toString sort ^ "\n") *)
                                  in
                                      Exis (ex, sort, g (sort, X.Evar ex, Tycon(tc, X.O (X.Evar ex), params)))
                                  end
                          | (SOME (X.Sorting.Nameless (sort, SOME default)), X.N) => (* Type is indexed with a default index *)
                                 Tycon(tc, X.O default, params)

                          | (SOME (X.Sorting.Nameless (sort, defaultIndex)), X.O i) => g (sort, i, A)
                          | (SOME (X.Sorting.Fields fieldspecs), X.I indices) =>
                                  let fun repeat_g [] texp = texp
                                        | repeat_g ((fieldname, i) :: rest) texp =
                                            let in case Assoc.getOpt fieldspecs fieldname of
                                                NONE => raise Option   (* should have been rejected by Sortcheck *)
                                              | SOME (sort, defaultIndex) => g (sort, i, repeat_g rest texp)
                                            end
                                  in
                                    repeat_g indices A
                                  end
                        end
                | texp => texp

          val foldspec = SdmlFold.texpSpec (transform_quantifiers o transform)
      in
          (*print ("INJECT INPUT: " ^ Print.pTexp texp ^ "\n");*)
          let val result = SdmlFold.fold_texp foldspec texp
          in
              (*print ("INJECTOUTPUT: " ^ Print.pTexp result ^ "\n");*)
              result
          end
      end
  
  fun inject_typing get (ctxt, texp) = (ctxt, inject_type get texp)
  fun inject_ctxanno get typings = List.map (inject_typing get) typings

  fun inject_anno get anno = case anno of 
       AnnotationType.Type A => AnnotationType.Type (inject_type get A)
     | AnnotationType.Some (sym, sort, anno) => AnnotationType.Some (sym, sort, inject_anno get anno)
     | AnnotationType.LeftProgramVar (pv, A, anno) => AnnotationType.LeftProgramVar (pv, A, inject_anno get anno)

  fun inject_annotation get annos = List.map (inject_anno get) annos
  
  fun inject_dectype get dectype = case dectype of
        Dectype.AGAINST annotation => Dectype.AGAINST (inject_annotation get annotation)
      | Dectype.TOPLEVEL_AGAINST texp => Dectype.TOPLEVEL_AGAINST (inject_type get texp)
      | Dectype.TOPLEVEL_NOT texp => Dectype.TOPLEVEL_NOT (inject_type get texp)

  fun inject_types program = program

(*
  fun inject_types (Program(libinfo as Libinfo{primtcs= primtcs, primops= primops, exception_tc= exception_tc}, typedecsl, locexp)) = 
      let val tcAssoc = getTcAssoc (primtcs, typedecsl)

          fun get_sort_opt tc =
              let val base_tc = case Datasorts.refines tc of SOME tc' => tc' | NONE => tc
              in
                  case Assoc.getOpt tcAssoc base_tc of
                      SOME stuff => stuff
                    | NONE => (print ("get_sort_opt: " ^ TC.toString tc ^ " not found\n"); raise Option)
              end

          fun transform_texp texp =
              case texp of
                  Tycon(tc, NONE(*User gave no index*), params) =>
                      let in case get_sort_opt tc of
                          NONE => 
                              let (* val _ = print ("type " ^ TC.toString tc ^ "  not refined\n") *)
                              in
                                  texp   (* Type `tc' is not refined:  Leave as is *)
                              end
                        | SOME (sort, NONE) => (* Type `tc' is refined with no default index:  Add existential quantifier *)
                              let val ex = IndexSym.fresh "ex"
                              (* val _ = print ("TYPE " ^ TC.toString tc ^ "  is refined, adding Exis\n") *)
                              in
                                  Exis(ex, sort, Tycon(tc, SOME (X.Evar ex), params))
                              end                              
                        | SOME (sort, SOME defaultIndex) => (* Type `tc' is refined with default index *)
                              Tycon(tc, SOME defaultIndex, params)
                         (* NOTE.  In the case of a product refinement, this scheme of having either an
                          existential *or* a specific index is going to fail.  A more general solution might
                          be to allow something like

                             primitive type real with (real * dim) = -exists a : real- real(a, NODIM)
                             primitive type real with dim = real(NODIM)
                         *)
                      end
                | texp => texp
                      
          val foldspec2 = SdmlFold.texpSpec transform_texp
              
          fun transform_con (Constructor {c, basetype, contype}) =
              Constructor{c= c, basetype= basetype, contype=SdmlFold.fold_texp foldspec2 contype}

          val foldspec1 = SdmlFold.conSpec transform_con
      in
          Program(Libinfo{primtcs= primtcs,
                          primops= map (fn (pv, texp) => (pv, SdmlFold.fold_texp foldspec2 texp)) primops,
                          distinguished= distinguished},
                  SdmlFold.fold_algsl foldspec1 typedecsl,
                  SdmlFold.fold_locexp foldspec2 locexp)
      end
*)

    fun transform_quantifiers_core texp =
        case texp of
            Univ(a, X.Subset(sort, a', P), A)  => 
                let val Psubstituted = X.Constraint.subst [(a', X.Uvar a)] P
                in
                    Univ(a, sort, Implies(Psubstituted, A))
                end
          | Exis(b, X.Subset(sort, b', P), B)  => 
                let val Psubstituted = X.Constraint.subst [(b', X.Evar b)] P
                in
                    Exis(b, sort, Conj(Psubstituted, B))
                end
          | texp => texp

  fun transform_quantifiers texp =
      SdmlFold.fold_texp (SdmlFold.texpSpec transform_quantifiers_core) texp

  fun clean texp =
      transform_quantifiers texp

  fun eliminate_subset_sorts (program as Program(libinfo as Libinfo{primtcs, primops, distinguished},
                                      lib_decs,
                                      locexp)) =

    (* "context" here is a full typedecsl *)
      let (* val _ = print ("eliminate_subset_sorts: " ^ Int.toString (List.length typedecsl) ^ "\n") *)
  
           fun get_sort_opt context tc =
              let val base_tc = case Datasorts.refines tc of SOME tc' => tc' | NONE => tc
                  val tcAssoc = getTcAssoc (primtcs, context)
              in
                  case Assoc.getOpt tcAssoc base_tc of
                      SOME stuff => stuff
                    | NONE => (print ("get_sort_opt: " ^ TC.toString tc ^ " not found\n"); raise Option)
              end
          
          fun g (sort, i, texp) =
              case sort of
                  X.Subset(sort, a, P) =>
                    let val Psubstituted = X.Constraint.subst [(a, i)] P
                    in
                        Conj(Psubstituted, texp)
                    end
                | X.Product (sort1 :: sorts)  =>
                    let in case i of
                               X.Tuple (i1 :: i's) => 
                                 g (X.Product sorts, X.Tuple i's, g (sort1, i1, texp))
                             | _ => g (X.Product sorts, i, g (sort1, i, texp))
                    end
                | sort => texp

          fun transform_typeapps context texp =
              case texp of
                  Tycon(tc, record, params) =>
                    let in case (record, get_sort_opt context tc) of
                          (X.N, _) => texp
                        | (X.O i, X.Sorting.Nameless (sort, defaultIndex)) => g (sort, i, texp)
                        | (X.I indices, X.Sorting.Fields fieldspecs) =>
                            let fun repeat_g [] texp = texp
                                  | repeat_g ((fieldname, i) :: rest) texp =
                                      let in case Assoc.getOpt fieldspecs fieldname of
                                          NONE => raise Option   (* should have been rejected by Sortcheck *)
                                        | SOME (sort, defaultIndex) => g (sort, i, repeat_g rest texp)
                                      end
                            in
                              repeat_g indices texp
                            end
                      end
                | texp => texp

          fun transform_datatype_indices_alg (dtype as Datatype _) =
                    let fun f (X.Subset (sort, a, P)) = f sort
                          | f (X.Product sorts) = X.Product (map f sorts)
                          | f sort = sort
                    in
                        updateSorting (X.Sorting.map (fn (sort, defaultIndex) => (f sort, defaultIndex)))
                                      dtype
                    end

            | transform_datatype_indices_alg (Synonym {tc, tv, params, definition}) = 
                  let  (*XXX? *)
                  in
                      Synonym {tc= tc, tv= tv, params= params, definition= definition}
                  end
                    
          fun transform_datatype_indices_algs typedecs =
              map transform_datatype_indices_alg typedecs

          fun transform_datatype_indices typedecsl =
              map transform_datatype_indices_algs typedecsl

          val swine_flu : typedecs list ref = ref []
          fun addSwine typedecsl = swine_flu := !swine_flu @ typedecsl
          fun amendSwine f =
            swine_flu := List.map f (!swine_flu)

          fun clearSwine () = swine_flu := []
 
          fun transform_quantifiers_after_typeapps texp =
            let val texp = if !SdmlFold.in_typedec then texp else transform_typeapps (!swine_flu) texp
                val texp = transform_quantifiers texp
            in
                texp
            end

          fun amend1 s1 s2 = case (s1, s2) of
             (X.Sorting.None, s2) => s2
           | (s1, X.Sorting.None) => s1
           | (X.Sorting.Nameless _, _) => raise Option   (* fail ("amend1 trying to amend nameless") *)
           | (_, X.Sorting.Nameless _) => raise Option   (* fail ("amend1 trying to amend with nameless") *)
           | (X.Sorting.Fields origFields, X.Sorting.Fields moreFields) =>
                   let val result =
                     X.Sorting.Fields (origFields @ moreFields)   (* XXX: check for clashes *)
                   in
                   ( print ("Inject: amend1: new sorting: " ^ X.Sorting.toString result ^ "\n")
                     ; result)
                   end

          fun amendSorting context tc sorting = case context of
             [] => []
           | (dtype as Datatype{tc= tc1, ...}) :: rest =>
                  if tc = tc1 then
                      updateSorting (fn sorting1 => amend1 sorting1 sorting) dtype
                      ::
                      rest
                  else
                      dtype :: (amendSorting rest tc sorting)
           | (syn as Synonym _) :: rest => 
                  syn :: (amendSorting rest tc sorting)

          fun horror dec = (let in case dec of
                  Dec _ => ()
                | Typedec typedecs => addSwine [typedecs]
                | DatatypeWith(tc, sorting) => amendSwine (fn typedecs => amendSorting typedecs tc sorting)
                | _ => ()   (* ??? *)
             end;
             dec)

(*
                              val foldspec_quantifier_transformation_only = SdmlFold.texpSpec (transform_quantifiers)
                              val swineulate = SdmlFold.decSpec horror
                              val foldspec_quantifier_transformation_and_typeapp_transformation = SdmlFold.texpSpec_dec transform_quantifiers_after_typeapps horror

                    (*
                              val _ = addSwine typedecsl
                    *)
                              val primops = map (fn (pv, {source_texp= source_texp, elaboration= elaboration, proper_name= proper_name, sanitized_name= sanitized_name}) =>
                                                    (pv, {source_texp= SdmlFold.fold_texp foldspec_quantifier_transformation_and_typeapp_transformation source_texp,
                                                    elaboration= elaboration, proper_name= proper_name, sanitized_name= sanitized_name}))
                                                 primops
                              val typedecsl = (* transform_datatype_indices (SdmlFold.fold_algsl foldspec_quantifier_transformation_only typedecsl) *)
                                          []
                              val locexp = SdmlFold.fold_locexp (SdmlFold.algSpec transform_datatype_indices_alg) locexp
                              val _ = clearSwine()
                    (*
                              val _ = addSwine typedecsl
                    *)
                              val _ = SdmlFold.fold_locexp swineulate locexp
                    (*          val _ = print (P.p P.printTypedecsl (!swine_flu) ^ "\n") *)
                              val body = SdmlFold.fold_locexp foldspec_quantifier_transformation_and_typeapp_transformation locexp
                    (*          val _ = print "body.\n" *)
*)

      in
          program
(*
                              Program(Libinfo{primtcs= primtcs,
                                              primops= primops, 
                                              distinguished= distinguished},
                    (*                  SdmlFold.fold_algsl foldspec typedecsl,
                      There is a problem with transforming the datacon signature, as shown in an example:

                       datacon Nil : list(0)
                       ...
                       datatype list with nat = Nil | ...

                       Here Nil's type will be converted from  list(0)  to  [0 >= 0] list(0)  (i.e., Conj(0 >= 0, list(0))).
                       This is morally harmless, but Typecheck cannot handle any
                       disjunctive form (including Conj) in constructor signatures. 
                       It is morally harmless only because 0 >= 0 holds.
                       If we instead had

                         datacon Nil : list(~1)

                       all hell would break loose.

                       Probably the right thing to do is to "validate" the signature by
                       building and solving constraints (e.g., 0 >= 0 in the above
                       example), to check that each data constructor really does construct
                       an object indexed by a member of the subset sort.

                       Note that we must still transform *quantifiers* in datacon types:
                            -all u:nat-  ---> -all u:int- {u >= 0}
                       and correspondingly for -exists-.  But we must not add Conj
                       constraints "around" Typeapps.

                       For now, the burden is on the user to verify that Nil : list(~1) is
                       not perpetrated.
                    *)
                                      lib_decs,
                                      body)
*)
      end

fun flatten_productsort_quantifiers program = 
      let
      in
          program
(*          SdmlFold.fold_program_including_primops foldspec program *)
      end

end (* structure Inject *)
