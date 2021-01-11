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
signature PARSELIB = 
sig

    (* Clear symbol table *)

    datatype pvstatus =
          Neutral           (* undefined, and not forced to be a function (because of a forward reference)   formerly  NONE *)
        | FutureFun     (* undefined, but must be declared with `fun' because of a forward reference    formerly  NONE *)
        | DefinedFun   (* defined using `fun'     formerly  SOME () *)
        | DefinedVal    (* defined using `val'     formerly  SOME () *)

    (* Parsing environments *)
    datatype pvinfo =
        Ordvar of Sdml.Dectype.dectype option * pvstatus ref
      | Convar

    datatype tcinfo =
        SimpleType of Sdml.tc
      | Datasort of Sdml.tc * Sdml.tc   (* (datasort, simple type) *)
      | TypeSynonym of Sdml.tc * Sdml.tv   (* type synonyms (type declarations) are implemented as existential type variables *)

    type env

    (* Type constructors *)
    structure Type : sig
        val lookup : (string -> unit) -> env -> string -> tcinfo
        val lookup_soft : env -> string -> tcinfo option

        val get : string -> (string -> unit) -> env -> Sdml.tc

        (* lookup_simple_type: Get SimpleType, raise error otherwise *)
        val lookup_simple_type : (string -> unit) -> env -> string -> Sdml.tc

        (* lookup_type: Get tc, regardless of whether SimpleType or Datasort *)
        val lookup_type : (string -> unit) -> env -> string -> Sdml.tc

        val extend : env -> (string * tcinfo) list -> env

        val extend_libinfo : env -> (Sdml.tc * Indexing.Sorting.t) -> env
    end

    (* Type variables *)
    structure Tyvar : sig
        val lookup : (string -> unit) -> env -> string -> Sdml.tv
        val lookup_soft : env -> string -> Sdml.tv option

        val extend : env -> (string * Sdml.tv) list -> env
        val clear : env -> env
    end

    (* Datasorts *)   
    val get_datasort : Sdml.tc -> env -> string -> (env * Datasorts.datasort)
    val process_subsortpairs : Sdml.tc -> env -> (string * string) list -> env

    structure Pvar : sig
    (* Program variables, including data constructors (but see also Con below) *)
        val lookup : (string -> unit) -> env -> string -> (pvinfo * Sdml.pv)
        val lookup_soft : env -> string -> (pvinfo * Sdml.pv) option
        (*   val extend : env -> (string * Sdml.pv) list -> env *)
        val extendOpt : env -> (string * Sdml.pv * Sdml.Dectype.dectype option * pvstatus)  list -> env
        val extend_DefinedVal : env -> (string * Sdml.pv (* implied: NONE,  -XXX SOME () XXX- *))  list -> env

        val extend_libinfo_primop : env -> (Sdml.pv * Sdml.primopinfo) -> env

        val tupleize : PV.sym list -> Sdml.locexp -> Sdml.exp
    end

    (* Data constructors *)
    structure Con : sig
        val extend : env -> (string * Sdml.pv) -> env

        val get_bool : (string -> unit) -> env -> {true : Sdml.pv, false : Sdml.pv}
        val get_list : (string -> unit) -> env -> {nil : Sdml.pv, cons : Sdml.pv}
    end

   (* Index-level variables (iv) and sorts (is) *)
        val lookup_iv : (string -> unit) -> env -> string -> (IndexSym.sym * Indexing.syminfo)
        val lookup_is : (string -> unit) -> env -> string -> (IndexSortSym.sym * Indexing.sort)

        val extend_iv : env -> (string * (IndexSym.sym * Indexing.syminfo)) list -> env
        val extend_is : env -> (string * (IndexSortSym.sym * Indexing.sort)) list -> env

        val extend_fields : env -> (string * (IndexFieldName.sym * Indexing.fieldsyminfo)) list -> env
        val lookup_field : (string -> unit) -> env -> string -> (IndexFieldName.sym * Indexing.fieldsyminfo)

    (* Top-level *)

    val get_libinfo : env -> Sdml.libinfo

    val get_empty_env : unit -> env
    val reset : unit -> unit
   
end (* signature PARSELIB *)



structure ParseLib :> PARSELIB = 
struct

  structure X = Indexing
  structure DS = Datasorts
  structure SDE = StringEnv 

  val {dprint, ...} =
          Debug.register {full_name= "ParseLib",
                          short_name= "ParseLib"}
  
  local
      val index = Option.valOf (Debug.from "ParseLib")
  in
      fun fail s =
          Debug.makeFail index s
  end

  (* Symbol tables *)
  fun base_ivenv() = SDE.empty ()

  fun reset () =
      (TV.reset ();
       TC.reset ();
       PV.reset ())
   
  datatype pvstatus =
      Neutral
    | FutureFun
    | DefinedFun
    | DefinedVal
      
  datatype pvinfo =
      Ordvar of Sdml.Dectype.dectype option * pvstatus ref
    | Convar

  datatype tcinfo =
      SimpleType of Sdml.tc
    | Datasort of Sdml.tc * Sdml.tc
    | TypeSynonym of Sdml.tc * Sdml.tv

  datatype env = Env of {tcenv : tcinfo SDE.env,
                         pvenv : (pvinfo * PV.sym) SDE.env, 
                         tvenv : TV.sym SDE.env,
                         ivenv : (IndexSym.sym * X.syminfo) SDE.env,
                         sortenv : (IndexSortSym.sym * X.sort) SDE.env,
                         fieldenv : (IndexFieldName.sym * X.fieldsyminfo) SDE.env,
                         libinfo : Sdml.libinfo}

  fun updateTcenv (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = f tcenv,
           pvenv = pvenv,
           tvenv = tvenv,
           ivenv = ivenv,
           sortenv = sortenv,
           fieldenv = fieldenv, 
           libinfo = libinfo}

  fun updatePvenv (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = tcenv,
           pvenv = f pvenv,
           tvenv = tvenv,
           ivenv = ivenv,
           sortenv = sortenv,
           fieldenv = fieldenv, 
           libinfo = libinfo}

  fun updateTvenv (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = tcenv,
           pvenv = pvenv,
           tvenv = f tvenv,
           ivenv = ivenv,
           sortenv = sortenv,
           fieldenv = fieldenv, 
           libinfo = libinfo}

  fun updateIvenv (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = tcenv,
           pvenv = pvenv,
           tvenv = tvenv,
           ivenv = f ivenv,
           sortenv = sortenv,
           fieldenv = fieldenv, 
           libinfo = libinfo}

  fun updateSortenv (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = tcenv,
           pvenv = pvenv,
           tvenv = tvenv,
           ivenv = ivenv,
           sortenv = f sortenv,
           fieldenv = fieldenv, 
           libinfo = libinfo}

  fun updateFieldenv (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = tcenv,
           pvenv = pvenv,
           tvenv = tvenv,
           ivenv = ivenv,
           sortenv = sortenv,
           fieldenv = f fieldenv, 
           libinfo = libinfo}

  fun updateLibinfo (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) f = 
      Env {tcenv = tcenv,
           pvenv = pvenv,
           tvenv = tvenv,
           ivenv = ivenv,
           sortenv = sortenv,
           fieldenv = fieldenv, 
           libinfo = f libinfo}


  fun set_distinguished (Sdml.Libinfo{primtcs=primtcs, primops=primops, distinguished= distinguished}) distinguished' = 
      Sdml.Libinfo {primtcs= primtcs, primops= primops, distinguished= distinguished'}

  structure Type = struct
      fun lookup_soft (Env{tcenv,...}) name =  SDE.get tcenv name

      fun lookup report env name = 
            case lookup_soft env name of
              NONE => (report ("type constructor `" ^ name ^ "' not defined");
                       fail "")
            | SOME stuff => stuff

      fun get tc report env =
          case lookup_soft env tc of
            NONE => (report ("constant of type `" ^ tc ^ " used, but type is not defined");
                     fail "")
          | SOME (SimpleType tc) => tc
          | SOME (Datasort _) => (report (tc^" constant used but type constructor `"^tc^"' is a datasort, not a type");
                     fail "")

      fun lookup_simple_type report env name = 
            case lookup report env name of
                SimpleType tc => tc
              | Datasort _ => (report ("type `" ^ name ^ "' a datasort, not a simple type");
                     fail "")
              | TypeSynonym _ => (report ("type `" ^ name ^ "' a synonym, not a simple type");
                     fail "")

      fun lookup_type report env name = 
          case lookup report env name of
              SimpleType tc => tc
            | Datasort (ds, _) => ds
            | TypeSynonym (tc, _) => tc

      fun extend (Env {tcenv, pvenv, tvenv, ivenv, sortenv, fieldenv, libinfo}) bindings = 
          let val libinfo =
                  let fun setExn (libinfo as Sdml.Libinfo{distinguished= distinguished as {exnTC, intTC, stringTC, sumTC, inl_pv, inr_pv}, ...}) = 
                            case List.find (fn (s, _) => s = "exn") bindings of
                                SOME (s, SimpleType exnTC) =>
                                     set_distinguished libinfo {exnTC= exnTC, intTC= intTC, stringTC= stringTC, sumTC= sumTC, inl_pv= inl_pv, inr_pv= inr_pv}
                              | _ => libinfo

                      fun setInt (libinfo as Sdml.Libinfo{distinguished= distinguished as {exnTC, intTC, stringTC, sumTC, inl_pv, inr_pv}, ...}) = 
                            case List.find (fn (s, _) => s = "int") bindings of
                                SOME (s, SimpleType intTC) =>
                                       set_distinguished libinfo {exnTC= exnTC, intTC= intTC, stringTC= stringTC, sumTC= sumTC, inl_pv= inl_pv, inr_pv= inr_pv}
                              | _ => libinfo

                       fun setString (libinfo as Sdml.Libinfo{distinguished= distinguished as {exnTC, intTC, stringTC, sumTC, inl_pv, inr_pv}, ...}) = 
                            case List.find (fn (s, _) => s = "string") bindings of
                                SOME (s, SimpleType stringTC) =>
                                    set_distinguished libinfo {exnTC= exnTC, intTC= intTC, stringTC= stringTC, sumTC= sumTC, inl_pv= inl_pv, inr_pv= inr_pv}
                              | _ => libinfo

                       fun setSum (libinfo as Sdml.Libinfo{distinguished= distinguished as {exnTC, intTC, stringTC, sumTC, inl_pv, inr_pv}, ...}) = 
                            case List.find (fn (s, _) => s = "sum") bindings of
                                SOME (s, SimpleType sumTC) =>
                                    set_distinguished libinfo {exnTC= exnTC, intTC= intTC, stringTC= stringTC, sumTC= sumTC, inl_pv= inl_pv, inr_pv= inr_pv}
                              | _ => libinfo

                       val libinfo = setExn libinfo
                       val libinfo = setInt libinfo
                       val libinfo = setString libinfo
                       val libinfo = setSum libinfo
                  in
                      libinfo
                  end
          in
              Env {tcenv = SDE.extend tcenv bindings,
                   pvenv = pvenv, 
                   tvenv = tvenv,
                   ivenv = ivenv,
                   sortenv = sortenv,
                   fieldenv = fieldenv, 
                   libinfo = libinfo}
          end

      fun extend_libinfo env (tc, sorting) = 
           updateLibinfo env (fn Sdml.Libinfo{primtcs=primtcs, primops=primops, distinguished= distinguished} =>
                              Sdml.Libinfo{primtcs= (tc, sorting) :: primtcs, primops= primops, distinguished= distinguished})
  end


  structure Tyvar = struct
      fun lookup report (Env{tvenv, ...}) name = 
        case SDE.get tvenv name of
          NONE => (report ("undefined type variable: " ^ name);
                   fail "")
        | SOME tv => tv

      fun lookup_soft (Env{tvenv, ...}) name = SDE.get tvenv name

      fun extend env bindings = 
          updateTvenv env (fn tvenv => SDE.extend tvenv bindings)

      fun clear env =
          updateTvenv env (fn _ => SDE.empty())
  end

  structure Pvar = struct
      fun lookup_soft (Env{pvenv,...}) name =
        SDE.get pvenv name

      fun lookup report env name = 
          case lookup_soft env name of
              NONE => (report ("undefined variable or constructor: " ^ name);
                       fail "")
            | SOME stuff => stuff

      fun extend env bindings = 
          updatePvenv env (fn pvenv => SDE.extend pvenv bindings)

      fun extend_libinfo_primop env (pv, primopinfo) = 
           updateLibinfo env (fn Sdml.Libinfo{primtcs=primtcs, primops=primops, distinguished= distinguished} =>
                              Sdml.Libinfo{primtcs = primtcs, primops= (pv, primopinfo) :: primops, distinguished= distinguished})

      fun extendOpt env bindings =
         extend env (List.map (fn (s, pv, texpOpt, pvstatus) => (s, (Ordvar (texpOpt, ref pvstatus), pv))) bindings)

      fun extend_DefinedVal env bindings =
         extend env (List.map (fn (s, pv) => (s, (Ordvar (NONE, ref DefinedVal), pv))) bindings)

      fun tupleize [pv] (loc, exp) = Sdml.Fn(pv, (loc, exp))
        | tupleize (pvl as (_::_::_)) (loc, exp) =
              let val tuple = PV.fresh "tuplearg"
                  fun aux n [] = (loc, exp)
                    | aux n (pv :: pvl) =
                          let val rhs = (loc, Sdml.Proj(Int.toString n, (loc, Sdml.Var tuple)))
                          in
                              (loc, Sdml.Let([(loc, Sdml.Dec(pv, Sdml.ValKW, rhs))], aux (n + 1) pvl))
                          end
              in
                  Sdml.Fn(tuple, aux 1 pvl)
              end
        | tupleize [] (loc, exp) =
              let val unit = PV.fresh "unitarg"
              in 
                  Sdml.Fn (unit, (loc, exp))
              end

  end

  structure Con = struct
      fun extend env (s, pv) =
          let
      (*        val _ = print ("ParseLib.Con.extend: " ^ Separate.list ", " (List.map (fn (string, c) => "(\"" ^ string ^ "\", " ^ PV.toString c ^ ")") bindings) ^ "\n") *)
              (* Extend *)
              val env = Pvar.extend env (map (fn (s, c) => (s, (Convar, c))) [(s, pv)])

              (* Tedious check whether any newly bound constructor is "inl" or "inr", *and* is the first so named;
               if so, update inl_pv and/or inr_pv *)
              fun setInl (libinfo as Sdml.Libinfo{distinguished= distinguished as {exnTC, intTC, stringTC, sumTC, inl_pv, inr_pv}, ...}) = 
                  if PV.isNonsense inl_pv
                     andalso (s = "Inl")
                  then
                      set_distinguished libinfo {exnTC= exnTC, intTC= intTC, stringTC= stringTC, sumTC= sumTC,
                                                 inl_pv= pv, inr_pv= inr_pv}
                  else libinfo

              fun setInr (libinfo as Sdml.Libinfo{distinguished= distinguished as {exnTC, intTC, stringTC, sumTC, inl_pv, inr_pv}, ...}) = 
                  if PV.isNonsense inr_pv
                     andalso (s = "Inr")
                  then
                      set_distinguished libinfo {exnTC= exnTC, intTC= intTC, stringTC= stringTC, sumTC= sumTC,
                                                 inl_pv= inl_pv, inr_pv= pv}
                  else libinfo

              val env = updateLibinfo env setInl
              val env = updateLibinfo env setInr
          in
              env
          end

      fun get_named_pv (env as Env {pvenv, ...}) all_names (report, message) =
          let fun test names = case names of
                    [] => (report (message ^ " constructor `" ^ Separate.list " / " all_names ^ "' not defined");
                           fail "")
                  | name :: names => 
                        let in
                            case SDE.get pvenv name of
                                SOME (Convar, pv) => pv
                              | _ => get_named_pv env names (report, message)
                        end
          in
              test all_names
          end

      fun get_bool report env = 
          {true= get_named_pv env ["true"] (report, "bool"),
           false= get_named_pv env ["false"] (report, "bool")}

      fun get_list report env =
          {nil= get_named_pv env ["nil"] (report, "list"),
           cons= get_named_pv env ["::", "Cons"] (report, "list")}
  end



  fun extend_iv env bindings = 
      updateIvenv env (fn ivenv => SDE.extend ivenv bindings)

  fun extend_is env bindings = 
      updateSortenv env (fn sortenv => SDE.extend sortenv bindings)

  fun extend_pv env bindings = 
      updatePvenv env (fn pvenv => SDE.extend pvenv bindings)

  fun extend_fields env bindings = 
      updateFieldenv env (fn fieldenv => SDE.extend fieldenv bindings)
  
  fun extend_libinfo_primop env (pv, primopinfo) = 
       updateLibinfo env (fn Sdml.Libinfo{primtcs=primtcs, primops=primops, distinguished= distinguished} =>
                          Sdml.Libinfo{primtcs = primtcs, primops= (pv, primopinfo) :: primops, distinguished= distinguished})

  
  fun lookup_iv report (Env{ivenv,...}) name = 
    case SDE.get ivenv name of
      NONE => (report ("undefined index variable: " ^ name);
                    fail "")
    | SOME stuff => stuff

  fun lookup_is report (Env{sortenv, ...}) name =
      case SDE.get sortenv name of
          NONE => (report ("undefined index sort name: " ^ name);
                   fail "")
        | SOME stuff => stuff

  fun lookup_field report (Env{fieldenv, ...}) name =
      case SDE.get fieldenv name of
          NONE => (report ("unknown field name: " ^ name);
                   fail "")
        | SOME stuff => stuff

  fun get_datasort tc (env as Env {tcenv, ...}) id = 
      case SDE.get tcenv id of
          NONE => let val ds = TC.fresh id
                      val env' = Type.extend env [(id, Datasort(ds, tc))]
                  in
                      (env', ds)
                  end
        | SOME (Datasort(ds, tc)) => (env, ds)
        | SOME (SimpleType tc) => (env, tc)   (* XXX ?? *)
        | SOME (TypeSynonym _) =>
              (print ("get_datasort: type `" ^ TC.toString tc ^ "' a synonym\n");
                   fail "")




  fun base_sortenv () =
      let val int = X.getIntSort()
          val bool = X.getBoolSort()
          val dim = X.getDimSort()
      in
          SDE.extend (SDE.empty ())
                     [
                      ("int", (int, X.Base int)),
                     ("bool", (bool, X.Base bool)),
                     ("dim", (dim, X.Base dim))
                     ]
      end

  fun get_empty_env () =
      Env{
          tvenv = SDE.empty (),
          pvenv = SDE.extend (SDE.empty ()) [],
          tcenv = (DS.reset(); SDE.extend (SDE.empty ()) []) (* (map (fn (tc, name) => (name, SimpleType tc)) tcs)) *),
          ivenv = ( (*Indexing.reset (); *) base_ivenv()),
          sortenv = base_sortenv(),
          fieldenv = SDE.empty (),
          libinfo = Sdml.Libinfo {primtcs= [],
                                 primops= [],
                                 distinguished= {exnTC= TC.fromInt ~1,
                                                 intTC= TC.fromInt ~2, 
                                                 stringTC= TC.fromInt ~3,
                                                 sumTC= TCExtra.sum,
                                                 inl_pv = PVExtra.inl,
                                                 inr_pv = PVExtra.inr}}
     }

  fun get_libinfo (Env{libinfo, ...}) = libinfo


  fun process_subsortpairs tc env [] = env
    | process_subsortpairs tc env ((id1, id2) :: pairs) =
          let val _ = DS.includeType tc
              val (env, d1) = get_datasort tc env id1 
    (*        val _ = print ("process_subsortpairs:  " ^ id1 ^ " --> #" ^ Int.toString (TC.toInt d1) ^ "; " ^
                             TC.toString d1 ^ "\n")
    *)
              val (env, d2) = get_datasort tc env id2
              val _ = DS.addDatasort (tc, d1)
              val _ = DS.addDatasort (tc, d2)
              val _ = DS.addPair (d1, d2)
          in
              process_subsortpairs tc env pairs
          end

end (* structure ParseLib *)
