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
signature SDMLFOLD = sig
  type spec

  val texpSpec : (Sdml.texp -> Sdml.texp) -> spec
  val typedecSpec : (Sdml.typedec -> Sdml.typedec) -> spec
  val conSpec : (Sdml.con -> Sdml.con) -> spec
  val expSpec : (Sdml.exp -> Sdml.exp) -> spec
  val armSpec : (Sdml.arm -> Sdml.arm) -> spec
  val decSpec : (Sdml.dec -> Sdml.dec) -> spec
  val programSpec : (Sdml.program -> Sdml.program) -> spec
  val compose : spec -> spec -> spec

  val fold_texp : spec -> Sdml.texp -> Sdml.texp
  val fold_exp : spec -> Sdml.exp -> Sdml.exp
  val fold_locexp : spec -> Sdml.locexp -> Sdml.locexp
  val fold_program : spec -> Sdml.program -> Sdml.program
  val fold_decs : spec -> Sdml.decs -> Sdml.decs
  val fold_program_including_primops : spec -> Sdml.program -> Sdml.program

  val in_typedec : bool ref

end (* signature SDMLFOLD *)


structure SdmlFold :> SDMLFOLD = struct
    open Sdml
    
    datatype spec =
           S of {ftexp : texp -> texp,
                 ftypedec : typedec -> typedec,
                 fcon : con -> con,
                 fexp : exp -> exp,
                 farm : arm -> arm,
                 fdec : dec -> dec,
                 fprogram : program -> program}
    
    val in_typedec = ref false

    
    fun id x = x

    fun texpSpec ftexp = S{ftexp= ftexp, ftypedec= id, fcon= id, fdec= id, fexp= id, farm= id, fprogram= id}
    fun typedecSpec ftypedec = S{ftexp= id, ftypedec= ftypedec, fcon= id, fdec= id, fexp= id, farm= id, fprogram= id}
    fun conSpec fcon = S{ftexp= id, ftypedec= id, fcon= fcon, fdec= id, fexp= id, farm= id, fprogram= id}
    fun expSpec fexp = S{ftexp= id, ftypedec= id, fcon= id, fdec= id, fexp= fexp, farm= id, fprogram= id}
    fun armSpec farm = S{ftexp= id, ftypedec= id, fcon= id, fdec= id, fexp= id, farm= farm, fprogram= id}
    fun decSpec fdec = S{ftexp= id, ftypedec= id, fcon= id, fdec= fdec, fexp= id, farm= id, fprogram= id}
    fun programSpec fprogram = S{ftexp= id, ftypedec= id, fcon= id, fdec= id, fexp= id, farm= id, fprogram= fprogram}


    fun compose (S{ftexp= ftexp1, ftypedec= ftypedec1, fcon= fcon1, fdec= fdec1, fexp= fexp1, farm= farm1, fprogram= fprogram1})
                (S{ftexp= ftexp2, ftypedec= ftypedec2, fcon= fcon2, fdec= fdec2, fexp= fexp2, farm= farm2, fprogram= fprogram2})
        =
                (S{ftexp= ftexp1 o ftexp2,
                   ftypedec= ftypedec1 o ftypedec2,
                   fcon= fcon1 o fcon2,
                   fdec= fdec1 o fdec2,
                   fexp= fexp1 o fexp2,
                   farm= farm1 o farm2,
                   fprogram= fprogram1 o fprogram2
               })
    
    fun fold_texp (spec as S{ftexp= ftexp, ...}) A = 
        let val f = fold_texp spec
        in 
            case A of
                Typevar g => ftexp A
              | Extypevar g => ftexp A
              | All (tyvar, uu, texp) => ftexp (All (tyvar, uu, f texp))
              | Arrow (texp1, texp2) => ftexp (Arrow (f texp1, f texp2))
              | Sect (texp1, texp2) => ftexp (Sect (f texp1, f texp2))
              | Rsect (texp1, texp2) => ftexp (Rsect (f texp1, f texp2))
              | Univ (a, sort, texp) => ftexp (Univ(a, sort, f texp))
              | Exis (a, sort, texp) => ftexp (Exis(a, sort, f texp))
              | Union (texp1, texp2) => ftexp (Union (f texp1, f texp2))
              | Runion (texp1, texp2) => ftexp (Runion (f texp1, f texp2))
              | Product texps => ftexp (Product (List.map f texps))
              | Tycon (tc, xexp, texps) => ftexp (Tycon (tc, xexp, List.map f texps))
              | Top => ftexp A
              | Bot => ftexp A
              | Implies (p, texp) => ftexp (Implies (p, f texp))
              | Record (fld, texp) => ftexp (Record (fld, f texp))
              | Conj (p, texp) => ftexp (Conj (p, f texp))
        end

(*
    fun fold_cc spec anno =
        List.map (fn (concrete_ctxt, texp) => (concrete_ctxt, fold_texp spec texp)) anno
*)

    fun fold_anno spec anno = case anno of
         AnnotationType.Type A => AnnotationType.Type (fold_texp spec A)
       | AnnotationType.LeftProgramVar (x, A, anno) => AnnotationType.LeftProgramVar (x, A, fold_anno spec anno)
       | AnnotationType.Some (a, sort, anno) => AnnotationType.Some (a, sort, fold_anno spec anno)

    fun fold_annolist spec annolist =
        List.map (fold_anno spec) annolist

    fun fold_dectype spec dectype = case dectype of 
          Dectype.AGAINST anno => Dectype.AGAINST (fold_annolist spec anno)
        | Dectype.TOPLEVEL_AGAINST texp => Dectype.TOPLEVEL_AGAINST (fold_texp spec texp)
        | Dectype.TOPLEVEL_NOT texp => Dectype.TOPLEVEL_NOT (fold_texp spec texp)

    fun fold_typedecs spec = List.map (fold_typedec spec)
            
    and fold_typedec (spec as S{ftypedec,...}) typedec = case typedec of
             Datatype {tc, builtin, params, sorting, constructors} =>
                 ftypedec (Datatype {tc= tc, builtin= builtin, params= params, sorting= sorting, constructors= fold_cons spec constructors})
           | Synonym {tc, tv, params, definition} =>
                 ftypedec (Synonym {tc= tc, tv= tv, params= params, definition= fold_texp spec definition})
                    
    and fold_cons spec = List.map (fold_con spec)

    and fold_con (spec as S{fcon,...})
                 (Constructor {c, nullary, basetype, contype, conjuncts, elaborated_conjuncts})
        =
          fcon (Constructor {c= c,
                              nullary= nullary,
                              basetype= fold_texp spec basetype,
                              contype= fold_texp spec contype,
                              conjuncts= fold_constructor_conjuncts spec conjuncts,
                              elaborated_conjuncts= fold_constructor_conjuncts spec elaborated_conjuncts
              })
        
    and fold_constructor_conjuncts spec conjuncts =
        List.map (fold_constructor_conjunct spec) conjuncts

    and fold_constructor_conjunct spec (pv, texp) =
        (pv, fold_texp spec texp)

    fun fold_decs spec = List.map (fold_dec spec)

    and fold_dec (spec as S{fdec, ...}) (loc, d) =
    (loc,  case d of
        ValType (x, dectype) =>  fdec (ValType (x, fold_dectype spec dectype))
      | Dec (x, kw, exp) =>  fdec (Dec (x, kw, fold_locexp spec exp))
      | Typedec typedecs =>
            let val _ = in_typedec := true
                val typedecs' = fold_typedecs spec typedecs
                val _ = in_typedec := false
            in
                fdec (Typedec typedecs')
            end
      | Datacon (x, texp) =>
            fdec (Datacon (x, fold_texp spec texp))

      | d as TyvarVariance (tv, variance) =>
            fdec d

      | d as DatatypeWith (tc, sorting) =>
            fdec d

      | d as TestSubtype (sense, (A, B)) =>
            fdec (TestSubtype (sense, (fold_texp spec A, fold_texp spec B)))
    )

    and fold_exps spec locexps = List.map (fold_locexp spec) locexps

    and fold_locexp spec (loc, e) = (loc, fold_exp spec e)

    and fold_exp (spec as S{fexp, ...}) exp =
        let val flocexp = fold_locexp spec
        in
            case exp of
                Const (texp, k) => fexp (Const (fold_texp spec texp, k))
              | Var _ => fexp exp
              | Con _ => fexp exp
              | Fn (x, exp) =>  fexp (Fn (x, flocexp exp))
              | App (exp1, exp2) =>  fexp (App (flocexp exp1, flocexp exp2))
              | Case (exp, arms) =>
                    let 
                        val arms' = fold_arms spec arms
                    in
                        fexp (Case (flocexp exp,arms'))
                    end
              | Conapp (pv, exp2) =>  fexp (Conapp (pv, flocexp exp2))
              | RecordExp (fld, exp2) =>  fexp (RecordExp (fld, flocexp exp2))
              | Tuple exps =>  fexp (Tuple (List.map flocexp exps))
              | Merge exps =>  fexp (Merge (List.map flocexp exps))
              | Proj (n, exp) =>  fexp (Proj (n, flocexp exp))
              | Let (decs,exp) =>  fexp (Let (fold_decs spec decs, flocexp exp))
              | Lethint (anno, locexp) =>  fexp (Lethint (fold_annolist spec anno, flocexp locexp))
              | Anno (locexp, anno) =>  fexp (Anno (flocexp locexp, fold_annolist spec anno))
              | LET (X, locexp, exp) => 
                    fexp (LET (X, flocexp locexp, fexp exp))
              | LETSLACK (X, locexp, exp) => 
                    fexp (LETSLACK (X, flocexp locexp, fexp exp))
              | Lvar x => fexp exp
              | Raise exp => fexp (Raise (flocexp exp))
              | Handle (exp1, x, exp2) =>
                   fexp (Handle (flocexp exp1, x, flocexp exp2))
              | Spy (stuff, exp1) => fexp (Spy (stuff, flocexp exp1))
              | Leftanno (stuff, exp1) => fexp (Leftanno (fold_leftanno spec stuff, flocexp exp1))
        end

    and fold_leftanno spec leftanno = case leftanno of
        LeftProgramVar (pv, texp) => LeftProgramVar (pv, fold_texp spec texp)

    and fold_arms spec arms = List.map (fold_arm spec) arms

    and fold_arm (spec as S{farm, ...}) (Arm (pat, exp)) =
        farm (Arm (pat, fold_locexp spec exp))

    fun fold_program (spec as S{fprogram, ...}) (Program (libinfo, decs, locexp)) =
        fprogram (Program (libinfo, fold_decs spec decs, fold_locexp spec locexp))

    fun fold_program_including_primops (spec as S{fprogram, ...}) (Program (Libinfo{primtcs, primops, distinguished}, decs, locexp)) =
        let val _ = in_typedec := false
        in
            fprogram (Program(Libinfo{primtcs= primtcs,
                            primops= List.map (fn (pv, {source_texp= source_texp, elaboration= elaboration, proper_name= proper_name, sanitized_name= sanitized_name}) =>
                                                         (pv, {source_texp= fold_texp spec source_texp, elaboration= elaboration, proper_name= proper_name, sanitized_name= sanitized_name})) primops,
                            distinguished= distinguished},
                    fold_decs spec decs,
                    fold_locexp spec locexp))
        end
end (* structure SdmlFold *)

