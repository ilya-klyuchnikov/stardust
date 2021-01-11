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
(* File: Indexing.sml
 * Author: Joshua Dunfield
 * Contents: Index refinement types and associated functions.
 *)

(*
  The question of separate namespaces/syntaxes for index variables vis-a-vis
  index sorts vis-a-vis propositions vis-a-vis program variables, etc.,  arises.

  Contextual typing annotations constrain the choices:

     - If index variables are separate (e.g. written "`id") from
     program variables, there is no ambiguity in contexts: if we see
     `id: we parse the remainder of the assumption as an index sort,
     and if we see id: we parse the remainder as a type.  (Note that
     an alternative might be to "pivot" on the separator: write x:type
     for ordinary variables and x::sort (or something) for index
     variables.)
     
     - OTOH, if index variables are in the same namespace (and
      we don't pivot on the separator), types and index sorts must have
      different namespaces, because x:nat is ambiguous if
      nat is both a type name and a sort name.
 
     - Index functions and predicates need not be separate, since
       P is distinct from foo:bar for all foo, bar.
*)

signature INDEXING = sig
 
  structure IF : SYMTAB
  type sym = IndexSym.sym
  type sortname = IndexSortSym.sym

(* Index exps: *)
  datatype exp = 
      Uvar of sym
    | Evar of sym
    | Nil of sym
    | True
    | False
    | NODIM
    | BaseDim of sym
    | Literal of sortname * string
    | App of sym * exp
    | Tuple of exp list
    | Proj of int * exp (* Proj from a tuple; int is 1-based *)

  type fieldname = IndexFieldName.sym

  datatype record =
      N
    | I of (fieldname * exp) list
    | O of exp
  
(* Index constraints: *)
  datatype constraint =
      EQ of sort * exp * exp
    | PRED of sym * exp
    | TRUE
    | AND of constraint * constraint
    | OR of constraint * constraint
    | IMPLIES of constraint * constraint
    | ALL of sym * sort * constraint
    | EXISTS of sym * sort * constraint

  and sort =
      Base of sortname
    | Subset of sort * sym * constraint
    | Product of sort list
    | List of sort

  type funinfo = {domain : sort, range : sort, complement : IndexSym.sym option}

  datatype syminfo = 
      IUVar of sort
    | IEVar of sort
    | IFun of funinfo list   (* List must be nonempty *)
(*    | IPred of sort            (* domain; range must be Boolean *)
  This has been replaced by IFun(_,range) where range is Base boolSort. *)
    | INil of sort
    | ITrue
    | IFalse
    | INODIM
    | IBaseDim

  type fieldsyminfo = unit

  datatype domain_sig =
      Domainsig of {basesorts : sortname list,      (* Set of base sort names *)
                    funpreds : (sym * syminfo) list,    (* Index funpreds with info: whether fun or pred, sorting information *)
                    solver : unit}  (* Constraint solver (?) *)

  structure Sorting : sig
      type spec = sort * exp option
      datatype t =
        None
      | Nameless of spec
      | Fields of (fieldname * spec) list
      
      val specToString : spec -> string
      val toString : t -> string
      val map : (spec -> spec) -> t -> t
      val app : (spec -> unit) -> t -> unit
  end

  val reset : unit -> unit
  
  val lookupFun : string -> IndexSym.sym
  val getSyminfo : sym -> syminfo option
  val complementOf : sym -> IndexSym.sym
  val addFun : sym * syminfo -> unit
  val getIntSort : unit -> sortname
  val isIntSort : sort -> bool
  val getBoolSort : unit -> sortname
  val getDimSort : unit -> sortname
  
  val mkAND : constraint * constraint -> constraint
     (* mkAND(c1, TRUE) = c1,   mkAND(TRUE, c2) = c2.
      Otherwise mkAND behaves as AND. *)

  val mkOR : constraint * constraint -> constraint
     (* mkOR(c1, TRUE) = mkOR(TRUE, c2) = TRUE.
      Otherwise mkOR behaves as OR. *)

  val mkIMPLIES : constraint * constraint -> constraint
     (* mkIMPLIES(c1, TRUE) = TRUE,   mkIMPLIES(TRUE, c2) = c2.
      Otherwise mkIMPLIES behaves as IMPLIES. *)

  val mkEQ : sort * exp * exp -> constraint
     (* mkEQ(sort, e, e) = TRUE.
      Otherwise mkEQ behaves as EQ. *)

  structure Sort : EQ_PR where type t = sort

  structure Exp : EQ_PR where type t = exp

  structure Constraint : sig
     include PR
     val ok : constraint -> bool
     val ok' : sym list -> constraint -> bool
     val subst : (sym * exp) list -> (constraint -> constraint)
     val freeVars : sym list -> constraint -> sym list     (* freeVars S W = FV(W) - S *)
     val free : sym -> constraint -> bool     (* sym free in constraint? *)
  end where type t = constraint

  val simplify : constraint -> constraint

  val free : sym -> exp -> bool     (* sym free in exp? *)

  val freeVars : sym list -> exp -> sym list     (* freeVars S e = FV(e) - S *)

 (* Index substitution: a finite map from vars to exps *)
  val subst : (sym * exp) list -> (exp -> exp)

  val subst_record : (sym * exp) list -> (record -> record)
  val eq_record : record * record -> bool
  val map_record : (exp -> exp) -> record -> record
  val app_record : (exp -> unit) -> record -> unit

  val subsort : sort * sort -> bool    (* This is a pseudo-subsorting relation, and should be
                                        interpreted as "mightBeSubsort": it ignores
                                        propositions in subset sorts. *)

  val dumpFunpreds : unit -> unit

end


(* The recommended abbreviation for the structure Indexing is X. *)

structure Indexing :> INDEXING = struct
  
 
  structure IV = IndexSym
  structure IS = IndexSortSym
  structure IF = IndexFieldName

  type sym = IndexSym.sym
  type sortname = IndexSortSym.sym

  datatype exp = 
      Uvar of sym
    | Evar of sym
    | Nil of sym
    | True
    | False
    | NODIM
    | BaseDim of sym
    | Literal of sortname * string
    | App of sym * exp
    | Tuple of exp list
    | Proj of int * exp
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  type fieldname = IndexFieldName.sym
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  datatype record =
      N
    | I of (fieldname * exp) list
    | O of exp
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  datatype constraint =
      EQ of sort * exp * exp
    | TRUE
    | PRED of sym * exp
    | AND of constraint * constraint
    | OR of constraint * constraint
    | IMPLIES of constraint * constraint
    | ALL of sym * sort * constraint
    | EXISTS of sym * sort * constraint
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  and sort =
      Base of sortname
    | Subset of sort * sym * constraint
    | Product of sort list
    | List of sort
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  type funinfo = {domain : sort, range : sort, complement : IndexSym.sym option}
  datatype syminfo =
      IUVar of sort
    | IEVar of sort
    | IFun of funinfo list
(*    | IPred of sort *)
    | INil of sort
    | ITrue
    | IFalse
    | INODIM
    | IBaseDim
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  type fieldsyminfo = unit
(* DO NOT WRITE COMMENTS HERE.  WRITE THEM IN THE SIGNATURE ABOVE. *)
  datatype domain_sig =
      Domainsig of {basesorts : sortname list,      (* Set of base sort names *)
                    funpreds : (sym * syminfo) list,    (* Index funpreds with info: whether fun or pred, sorting information *)
                    solver : unit}  (* Constraint solver (?) *)

  val intSort : IndexSortSym.sym option ref = ref NONE
  val boolSort : IndexSortSym.sym option ref = ref NONE
  val dimSort : IndexSortSym.sym option ref = ref NONE
(*
  val plusFun : IndexSym.sym option ref = ref NONE
  val minusFun : IndexSym.sym option ref  = ref NONE
  val timesFun : IndexSym.sym option ref  = ref NONE
  val divFun : IndexSym.sym option ref  = ref NONE

  val ltPred : IndexSym.sym option ref  = ref NONE
  val lteqPred : IndexSym.sym option ref  = ref NONE
  val gtPred : IndexSym.sym option ref  = ref NONE
  val gteqPred : IndexSym.sym option ref  = ref NONE
*)

  val domainSig : domain_sig option ref = ref NONE

 fun !! x = valOf (!x)

  fun baseDomainSig () =
      let
          val int = !!intSort
      in
          Domainsig{basesorts= [int],
                    funpreds= [],
                    solver= ()
                    }
      end

  fun reset () =
      (IndexSym.reset();

(*
       plusFun := SOME (IV.fresh "+");
       minusFun := SOME (IV.fresh "-");
       timesFun := SOME (IV.fresh "*");
       divFun := SOME (IV.fresh "/");

       ltPred := SOME (IV.fresh "<");
       lteqPred := SOME (IV.fresh "<=");
       gtPred := SOME (IV.fresh ">");
       gteqPred := SOME (IV.fresh ">=");
*)
       IndexSortSym.reset ();
       intSort := SOME (IS.fresh "int");
       boolSort := SOME (IS.fresh "bool");
       dimSort := SOME (IS.fresh "dim");
       (* When adding something here, also need to change base_sortenv() in ParseLib.sml *)
       domainSig := SOME (baseDomainSig())
      )

  fun getSyminfo sym =
      let fun find [] = NONE
            | find ((sym', info) :: rest) = if sym' = sym then SOME info else find rest
          val Domainsig{funpreds= funpreds, ...} = !!domainSig
      in
          find funpreds
      end

  fun lookupFun string =
      let fun find [] = (print ("Indexing.sml:lookupFun: can't find " ^ string ^ "\n"); raise Option)
            | find ((sym, _) :: rest) = if IV.toShortString sym = string then sym else find rest
          val Domainsig{funpreds= funpreds, ...} = !!domainSig
      in
          find funpreds
      end

  fun addFun (sym, info) =
      let val Domainsig{basesorts= basesorts, funpreds= funpreds, solver= solver} = !!domainSig
          fun remove sym funpreds =
              case funpreds of [] => []
                             | ((sym', info')::funpreds) => if sym=sym' then remove sym funpreds
                                                            else (sym', info')::(remove sym funpreds)
          val funpreds = (sym, info) :: (remove sym funpreds)
      in
          domainSig := SOME (Domainsig{basesorts= basesorts, funpreds= funpreds, solver= solver})
      end

  (* part c1 c2: used in mkIMPLIES; true iff a subformula of the form c1 => Q exists in c2 *)
  fun part c1 c2 = case c2 of
      AND(c21, c22) => part c1 c21 orelse part c1 c22
    | IMPLIES(c21, c22) => c1=c21 orelse part c1 c22
    | ALL(_,_,c2) => part c1 c2
    | EXISTS(_,_,c2) => part c1 c2
    | _ => false

  fun skewer c1 c2 = case c2 of
      AND(c21, c22) => AND(skewer c1 c21, skewer c1 c22)
    | IMPLIES(c21, c22) => if c1=c21 then c22 else IMPLIES(c21, skewer c1 c22)
    | ALL(a,sort,c2) => ALL(a,sort,skewer c1 c2)
    | EXISTS(a,sort,c2) => EXISTS(a,sort,skewer c1 c2)
    | c2 => c2

  fun mkAND (TRUE, c2) = c2
    | mkAND (c1, TRUE) = c1
    | mkAND (c1, c2) = AND (c1, c2)

  fun mkOR (TRUE, c2) = TRUE
    | mkOR (c1, TRUE) = TRUE
    | mkOR (c1, c2) = OR (c1, c2)

(*        if part c1 c2 then c2   (* Disturbingly, this optimization *)
                           else IMPLIES (c1, c2)   (*  greatly speeds up typechecking ubits.rml. *)
*)

  fun mkEQ (sort, e1, e2) =
      if e1 = e2 then TRUE
      else EQ(sort, e1, e2)


  fun subst' s (Uvar v) =
          let in case Assoc.getOpt s v of
               SOME e' => (*subst' s*) e'
             | NONE => Uvar v
          end
    | subst' s (Evar v) =
          let in case Assoc.getOpt s v of
               SOME e' => (*subst' s*) e'
             | NONE => Evar v
          end
    | subst' s (Nil sym) = Nil sym
    | subst' s (App (f, obj)) = App (f, subst' s obj)
    | subst' s (Literal stuff) = Literal stuff
    | subst' s (Tuple objs) = Tuple (map (subst' s) objs)
    | subst' s (Proj (n, obj)) = Proj (n, subst' s obj)
    | subst' s True = True
    | subst' s False = False
    | subst' s NODIM = NODIM
    | subst' s (BaseDim sym) = BaseDim sym

  fun subst s e =
      subst' s e

  fun subst_record s (I record) = I (List.map (fn (field, e) => (field, subst s e)) record)
    | subst_record s N = N
    | subst_record s (O e) = O (subst s e)
  
  fun free a i =
      let in case i of
          Uvar b => a=b
        | Evar b => a=b

        | Nil sym => false
        | BaseDim sym => false

        | App(f, obj) => free a obj
        | Tuple objs => List.exists (free a) objs
        | Proj(n, obj) => free a obj

        | Literal stuff => false
        | True => false
        | False => false
        | NODIM => false
      end

  fun freeVars vars exp =
      let in case exp of
          Uvar b => if MyList.contains b vars then [] else [b]
        | Evar b => if MyList.contains b vars then [] else [b]
        | Nil sym => []
        | BaseDim sym => []
        | App(f, e0) => freeVars vars e0
        | Tuple exps => MyList.elimDups (List.concat (map (freeVars vars) exps))
        | Proj(n, e0) => freeVars vars e0
        | Literal stuff => []
        | True => []
        | False => []
        | NODIM => []
      end

  structure SortExpConstraint = struct

    fun Sort_toString (Base sortname) = IS.toShortString sortname
      | Sort_toString (Subset (sort, sym, pred)) =
            "{" ^ IV.toShortString sym ^ ":" ^ Sort_toString sort
          ^ "|" ^ Constraint_toString pred ^ "}"
      | Sort_toString (Product []) = "Unit"
      | Sort_toString (Product sorts) = "(" ^ Separate.list " * " (map Sort_toString sorts) ^ ")"
      | Sort_toString (List sort) = "[" ^ Sort_toString sort ^ "]"
    
    and Exp_toString (Uvar v) = IV.toString v
       | Exp_toString (App (f, i)) =
              let 
                  val fname = IV.toShortString f
                  val doInfix =
                          case fname of
                              "+" => true
                            | "-" => true
                            | "*" => true
                            | "/" => true
                            | ">=" => true
                            | "<=" => true
                            | ">" => true
                            | "<" => true
                            | "=" => true
                            | _ => false
              in
                  case (doInfix, i) of
                          (true, Tuple[i1, i2]) => "(" ^ Exp_toString i1 ^ " " ^ fname ^ " " ^ Exp_toString i2 ^ ")"
                        | (_, i) => fname ^ " " ^ Exp_toString i
              end
       | Exp_toString (Literal (sortname, s)) = s (* IS.toShortString sortname *)
       | Exp_toString (Tuple i's) = "(" ^ Separate.list "," (map Exp_toString i's) ^ ")"
       | Exp_toString (Proj (n, i)) = "#" ^ Int.toString n ^ "(" ^ Exp_toString i ^ ")"
       | Exp_toString (Evar v) = "[E]"^IV.toString v
       | Exp_toString (Nil v) = IV.toString v ^ ":::nil"
       | Exp_toString (True) = "true"
       | Exp_toString (False) = "false"
       | Exp_toString (NODIM) = "NODIM"
       | Exp_toString (BaseDim sym) = IV.toShortString sym
    
    and quantified quantifier (a, sort, c) = "(" ^ quantifier ^ " " ^ IV.toString a ^ " : " ^ Sort_toString sort ^ ". " ^ Constraint_toString c ^ ")"
    and Constraint_toString (EQ (_, i1, i2)) = Exp_toString i1 ^ " = " ^ Exp_toString i2
       | Constraint_toString (TRUE) = "TRUE"
       | Constraint_toString (PRED (p, Tuple[e1,e2])) = Exp_toString e1 ^ " " ^ IV.toShortString p ^ " " ^ Exp_toString e2
       | Constraint_toString (PRED (p, e1)) = IV.toShortString p ^ "(" ^ Exp_toString e1 ^ ")"
       | Constraint_toString (AND (c1, c2)) = Constraint_toString c1 ^ " and " ^ Constraint_toString c2
       | Constraint_toString (OR (c1, c2)) = Constraint_toString c1 ^ " \\/ " ^ Constraint_toString c2
       | Constraint_toString (IMPLIES (c1, c2)) = "(" ^ Constraint_toString c1 ^ " => " ^ Constraint_toString c2 ^ ")"
       | Constraint_toString (EXISTS stuff) = quantified "exists" stuff
       | Constraint_toString (ALL stuff) = quantified "all" stuff
        
    fun Sort_eq (x, y) =  x = y

    fun Exp_eq (i1, i2) =  i1 = i2



   end (* struct SortExpConstraint *)

  (* Please, sir, may I have recursive modules? *)

  structure Sort : EQ_PR = struct
    type t = sort

    val toString = SortExpConstraint.Sort_toString
    val eq = SortExpConstraint.Sort_eq
  end

  structure Exp : EQ_PR = struct
    type t = exp

    val toString = SortExpConstraint.Exp_toString
    val eq = SortExpConstraint.Exp_eq
  end

  structure Constraint : sig
       include PR
       val ok : constraint -> bool
       val ok' : sym list -> constraint -> bool
       val subst : (sym * exp) list -> (constraint -> constraint)
       val freeVars : sym list -> constraint -> sym list     (* freeVars S W = FV(W) - S *)
       val free : sym -> constraint -> bool
    end where type t = constraint
   = struct
     type t = constraint

    val toString = SortExpConstraint.Constraint_toString

     fun ok_obj G (Uvar v) = MyList.contains v G
       | ok_obj G (Evar v) = MyList.contains v G
       | ok_obj G (Nil _) = true
       | ok_obj G (BaseDim _) = true
       | ok_obj G (True) = true
       | ok_obj G (False) = true
       | ok_obj G (NODIM) = true
       | ok_obj G (Literal _) = true
       | ok_obj G (App (_, obj)) = ok_obj G obj
       | ok_obj G (Tuple objs) = List.all (ok_obj G) objs
       | ok_obj G (Proj (n, Tuple objs)) = (1 <= n andalso n <= length objs) andalso ok_obj G (Tuple objs)
       | ok_obj G (Proj(n, obj)) = ok_obj G obj

     fun ok'' G (EQ (_, obj1, obj2)) = ok_obj G obj1 andalso ok_obj G obj2
       | ok'' _ TRUE = true
       | ok'' G (AND (c1, c2)) = ok' G c1 andalso ok' G c2
       | ok'' G (OR (c1, c2)) = ok' G c1 andalso ok' G c2
       | ok'' G (IMPLIES (c1, c2)) = ok' G c1 andalso ok' G c2
       | ok'' G (ALL (v, sort, body)) = ok' (v::G) body
       | ok'' G (EXISTS (v, sort, body)) = ok' (v::G) body

     and ok' G c = ( (* print ("Indexing.Constraint ok' ::: " ^ toString c ^ "\n");
                    print ("Indexing.Constraint.ok': " ^ Separate.list "," (map (PV.toString) G) ^ "\n"); *)
                    ok'' G c)

     fun ok c = ok' [] c

     fun substIndex s (EQ (sort, obj1, obj2)) = mkEQ(sort, subst s obj1, subst s obj2)
       | substIndex s TRUE = TRUE
       | substIndex s (PRED(p, e)) = PRED(p, subst s e)
       | substIndex s (AND (c1, c2)) = AND(substIndex s c1, substIndex s c2)
       | substIndex s (OR (c1, c2)) = OR(substIndex s c1, substIndex s c2)
       | substIndex s (ALL (a, sort, body)) = ALL(a, sort, substIndex s body)
       | substIndex s (EXISTS (a, sort, body)) = EXISTS(a, sort, substIndex s body)
       | substIndex s (IMPLIES (c1, c2)) = IMPLIES(substIndex s c1, substIndex s c2)

     fun Constraint_freeVars vars W =
         let in case W of
             EQ(_, e1, e2) => freeVars vars e1 @ freeVars vars e2
           | PRED(fsym, e) => freeVars vars e
           | TRUE => []
           | AND(W1, W2) => Constraint_freeVars vars W1 @ Constraint_freeVars vars W2
           | OR(W1, W2) => Constraint_freeVars vars W1 @ Constraint_freeVars vars W2
           | IMPLIES(W1, W2) => Constraint_freeVars vars W1 @ Constraint_freeVars vars W2
           | ALL(a, sort, W0) => Constraint_freeVars (a :: vars) W0
           | EXISTS(a, sort, W0) => Constraint_freeVars (a :: vars) W0
         end

     fun freeVars vars W = MyList.elimDups (Constraint_freeVars vars W)

     fun free var W =
         MyList.contains var (freeVars [] W)


     val subst = substIndex
  end

  structure Sorting = struct
      type spec = sort * exp option
      datatype t =
        None
      | Nameless of spec
      | Fields of (fieldname * spec) list
      
      fun specToString (sort, default) =
        Sort.toString sort
      ^ (case default of NONE => ""
                                | SOME exp => "=" ^ Exp.toString exp)

      fun fieldspecToString (fieldname, spec) =
        IF.toShortString fieldname ^ ":" ^ specToString spec
  
      fun map f t = case t of
         None => None
      | Nameless spec => Nameless (f spec)
      | Fields fields => Fields (List.map (fn (fieldname, spec) => (fieldname, f spec)) fields)

      fun app f t = case t of
         None => ()
      | Nameless spec => f spec
      | Fields fields => List.app (fn (fieldname, spec) => f spec) fields
      
      fun toString t = case t of
         None => "None"
      | Nameless spec => "Nameless " ^ specToString spec
      | Fields fields => "Fields " ^ Separate.list ", " (List.map fieldspecToString fields)
  end

  fun eq_record (r1, r2) = case (r1, r2) of
     (N, N) => true
   | (O exp1, O exp2) => Exp.eq (exp1, exp2)
   | (I fields1, I fields2) =>
        List.all (fn (fieldname1, exp1) =>
                        List.exists (fn (fieldname2, exp2) => (fieldname1 = fieldname2) andalso Exp.eq (exp1, exp2)) fields2)
                   fields1
   | (_, _) => false

  fun map_record f r = case r of
     N => N
   | O exp => O (f exp)
   | I fields => I (List.map (fn (fieldname, exp) => (fieldname, f exp)) fields)

  fun app_record f r = case r of
     N => ()
   | O exp => f exp
   | I fields => List.app (fn (fieldname, exp) => f exp) fields


  fun mkIMPLIES (TRUE, c2) = c2
    | mkIMPLIES (c1, TRUE) = TRUE
    | mkIMPLIES (c1, c2) =
      let fun it'() =        IMPLIES(c1, skewer c1 c2)
               (* not "it" because MLton violates the Definition by disallowing "it" valbinds *)
(*          val _ = print ("mkIMPLIES: " ^ Constraint.toString c1 ^ " => ...\n") *)
      in case c1 of EQ(_, e1, e2) => if e1 = e2 then ((*print "==\n"; *)  IMPLIES(c1, skewer c1 c2)) else it'()
    | _ => it'()
      end

  fun simplify (AND (c1, c2)) =
        let val c1' = simplify c1
            and c2' = simplify c2
        in
            case (c1', c2') of
                (c1', TRUE) => c1'
              | (TRUE, c2') => c2'
              | _ => AND(c1', c2')
        end
    | simplify (c as EQ (sort, obj1, obj2)) = if Exp.eq(obj1, obj2) then TRUE else c
    | simplify TRUE = TRUE
    | simplify (ALL (a, sort, c)) = let val c' = simplify c
                                    in case c' of
                                        TRUE => TRUE
                                      | c' => ALL (a, sort, c')
                                    end
    | simplify (EXISTS (a, sort, c)) = let val c' = simplify c
                                       in case c' of
                                           TRUE => TRUE
                                         | c' => EXISTS (a, sort, c')
                                    end

  fun getIntSort() = !!intSort
  fun isIntSort sort = case sort of
                                       Base sortname => (sortname = getIntSort())
                                 | _ => false
  fun getBoolSort() = !!boolSort
  fun getDimSort() = !!dimSort

  fun subsort (s1, s2) =
      case (s1, s2) of
          (Base sortname1, Base sortname2) =>
              sortname1 = sortname2
        | (Product sorts1, Product sorts2) =>
              List.all subsort (ListPair.zip (sorts1, sorts2))
        | (List sort1, List sort2) =>
              subsort (sort1, sort2)
        | (Subset (sort1, sym1, P1), Subset (sort2, sym2, P2)) =>
              subsort (sort1, sort2)
        | (Subset (sort1, sym1, P1), s2) =>
              subsort (sort1, s2)
        | (s1, Subset (sort2, sym2, P2)) =>
              subsort (s1, sort2)
        | (_, _) => false


 (* The data representation here is broken:
    there should be only one complement for each predicate.
    Instead we silently assume the predicate is the same for each "conjunct",
    which happens to be true, but it should really be
      IFun of complement option *  ... list
  *)
  fun complementOf p =
      case getSyminfo p of
          SOME (IFun ({complement= SOME complement, ...} :: _)) =>
            complement
        | SOME (IFun _) =>
            raise Option

  fun funinfoToString {domain= domain, range= range, complement= complement} =
      "{"
      ^ "domain= " ^ Sort.toString domain ^ ", "
      ^ "range= " ^ Sort.toString range ^ ", "
      ^ "complement= " ^ (case complement of NONE => "NONE" | SOME iv => IndexSym.toString iv)
      ^ "}"

  fun funpredToString (IFun(funinfos)) = "[" ^ Separate.list ",  " (map funinfoToString funinfos) ^ "]"

  fun dumpFunpreds () = 
      let val Domainsig{funpreds= funpreds, ...} = !!domainSig
          val funpredStrings = List.mapPartial (fn (iv, info) =>
                                                  let in case info of
                                                           IFun(funinfos) => SOME (IndexSym.toString iv ^ " |-> " ^ funpredToString info)
                                                         | _ => NONE
                                                  end)
                                               funpreds
      in
          print (Separate.list ";\n" funpredStrings ^ "\n")
      end

end
