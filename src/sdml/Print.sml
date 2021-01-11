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
(* Print: printing StardustML abstract syntax (as concrete StardustML syntax).
 *
 * Conventions:
 *     Functions beginning with `print' take a PrettyPrint.ppstream, etc.
 *     Functions beginning with `p' simply return a string.
 *     If you need a `p' version of some `print' function printFoo, just use
 *
 *               p printFoo foo
 *
 * If you need to output *Standard* ML, use PrintTarget (PrintTarget.sml),
 * which has the same signature, but produces rather different output.
 *)

signature PRINT = sig

  datatype deckind = INITIAL_STATE | TYPE | FUN | VAL | IRRELEVANT
    (* deckind irrelevant for Print, only used in PrintTarget --- should reorganize *)

  type ppstream = PrintLib.ppstream
  type ppconsumer = PrintLib.ppconsumer

  (* given a ppstream operation on 'a and an 'a, produce a string *)
  val p : (ppstream -> 'a -> unit) -> 'a -> string
  
  val pTexp : Sdml.texp -> string   (* pTexp = p printTexp *)
  val pDec : Sdml.locdec -> string
  val pTexps : string -> Sdml.texp list -> string    (* pTexp = p printTexp *)
  val pExp : Sdml.exp -> string
  val pLocexp : Sdml.locexp -> string
  val pTyping : Sdml.typing -> string
  val pAnnotation : Sdml.annotation -> string

  val print : TextIO.outstream -> Sdml.program -> unit
  val printTarget : TextIO.outstream -> Sdml.program -> unit


  val printTypedecs : ppstream -> Sdml.typedec list -> unit
  val printConcContext : ppstream -> Sdml.concrete_ctxt -> unit
  val printDatatype : ppstream
                              -> Sdml.typedec
                              -> string * string
                              -> unit
  val printArm : ppstream -> Sdml.arm -> unit
  val printArms : ppstream -> Sdml.arm list -> unit

  val printConst: ppstream -> Sdml.texp * string -> unit

  val printDec : ppstream -> deckind -> Sdml.locdec -> deckind
  val printDecl : ppstream -> deckind -> Sdml.locdec list -> deckind
  val printDecs : ppstream -> Sdml.locdec list -> unit
  
  val printLocexp : ppstream -> Sdml.locexp -> unit
  val printExp : ppstream -> Sdml.exp -> unit
  val printLocexpl : ppstream -> Sdml.locexp list -> unit
  val printExps : ppstream -> Sdml.locexp list -> unit

  val printIndexExp : int -> ppstream -> Indexing.exp -> unit
  val printIndexRecord :  ppstream -> Indexing.record -> unit
  val printSorting :  ppstream -> Indexing.Sorting.t -> unit
  
  val printProgram : ppstream -> Sdml.program -> unit

  val printPat : ppstream -> Sdml.pattern -> unit

  val printTexp : ppstream -> Sdml.texp -> unit
  val printTexpl : ppstream -> Sdml.texp list -> unit   (* prints comma-separated list *)
(*  val printTexps : int -> string -> ppstream -> Sdml.texp list -> unit *)
end (* signature PRINT *)


signature PRINTSOURCEEXTRA = sig

  include PRINT
  val printConstructor : ppstream -> bool(*printBar*) -> Sdml.con -> unit
  val printConstructors : ppstream -> bool(*printBar*) -> Sdml.con list -> unit

end


structure Print :> PRINTSOURCEEXTRA = struct
  open Sdml

  open PrintLib

  structure CC = ConcreteContext 
  
  structure X = Indexing
  structure PP = PrettyPrint
  
  datatype deckind = INITIAL_STATE | TYPE | FUN | VAL | IRRELEVANT
  
  type ppstream = PrintLib.ppstream
  type ppconsumer = PrintLib.ppconsumer
  
  val {dprint, ...} =
          Debug.register {full_name= "Print",
                          short_name= "Print"}
  
  local
      val index = Option.valOf (Debug.from "Print")
  in
      fun fail pps s =
          (PP.flush_ppstream pps;
           Debug.makeFail index s)
  end

  fun addPV pps pv = addString pps (PV.toString pv)
  fun addTC pps tc = addString pps (TC.toShortString tc)
  fun addTV pps tv = addString pps (TV.toShortString tv)
  fun addEXTV pps tv = addString pps ("'E" ^ Int.toString (TV.toInt tv))
  fun addIV pps iv = addString pps (IndexSym.toString (*IndexSym.toShortString*) iv)
  fun addFld pps fld = addString pps (IndexFieldName.toShortString fld)

  val p = PrintLib.p
  

  fun printSort pps sort =
      (addString pps (X.Sort.toString sort); addBreak pps 0)

  fun pSort sort = X.Sort.toString sort

(* precedence:
  0   outermost / already inside parentheses
  2   inside tuple
  4   inside relational operator (<, <=, etc.)
  6   inside additive operator (+, -, etc.)
  8   inside multiplicative operator (/, *, etc.)
 10   inside exponential *)
  fun printIndexExp prec pps exp =
      case exp of
          X.Uvar sym => addIV pps sym
        | X.Evar sym => addIV pps sym
        | X.Nil sym => addString pps "Nil"
        | X.True => addString pps "true"
        | X.False => addString pps "false"
        | X.Literal (_ (* XXX? ignoring type *), s) => addString pps s
        | X.App (sym, exp) =>
              let val opPrec = case IndexSym.toShortString sym of
                                       "<" => 4
                                     | "<=" => 4
                                     | "=" => 4
                                     | ">=" => 4
                                     | ">" => 4
                                     | "<>" => 4
                                     | "+" => 6
                                     | "-" => 6
                                     | "*" => 8
                                     | "/" => 8
                                     | "mod" => 8
                                     | "^" => 10
                                     | _ => 1000
                  val needOuter = prec > opPrec
              in
                  if needOuter then addString pps "(" else ();
                  if opPrec > 100 then
                      let in addIV pps sym;
                             addString pps "(";
                             printIndexExp 0 pps exp;
                             addString pps ")"
                      end
                  else
                      let val X.Tuple[first, second] = exp
                      in
                        printIndexExp opPrec pps first;
                        addString pps " ";
                        addString pps (IndexSym.toShortString sym);
                        addString pps " ";
                        printIndexExp (opPrec + 1) pps second
                      end;
                  if needOuter then addString pps ")" else ()
              end
        | X.Tuple exps =>
                let val lstfn = if prec > 2 then addList {left="(", right=")", separator=", "}
                                else sep ", "
                in
                    lstfn (printIndexExp 2) pps exps
                end
        | X.Proj (n, exp) =>
              (addString pps "#";
               addString pps (Int.toString n);
               addString pps "(";
               printIndexExp 0 pps exp;
               addString pps ")")
        | X.NODIM => addString pps "NODIM"
        | X.BaseDim sym => addString pps ("dim[" ^ IndexSym.toShortString sym ^ "]")

  fun printProp pps prop = addString pps (X.Constraint.toString prop)

  fun printTexps level delim pps texps =
      sep delim (printTexpAux level) pps texps


  and printTexpl pps [] = ()
    | printTexpl pps (A::As) =
          (addBreak pps 1;
           printTexpAux 60 pps A; (* 51 50 60 *)
           printTexpl pps As)


  and printIndexRecord pps record = case record of
      X.N => ()
    | X.O i => addList {left="[", right="]",  separator=";"} (fn pps => fn i => printIndexExp 0 pps i) pps [i]
    | X.I record =>
        addList {left="{", right= "}", separator= "; "}
           (fn pps => fn (field, xexp) =>
             (addFld pps field;
              addString pps "=";
              printIndexExp 0 pps xexp)
           )
           pps
           record

(* levels:
 0:  -all-  &  { }
10:  ->
20:  -exists-  [ ]
30:  *
40:  \/
50:  type application
*)
  and printTexpAux level pps texp =
    let fun LP threshold = if level > threshold then addString pps "(" else ()
        fun RP threshold = if level > threshold then addString pps ")" else ()
    in
      case texp of 
           Typevar tv => addTV pps tv
         | Extypevar tv => addEXTV pps tv
         | All(tv, uu, texp) => (addString pps "(-all";
                                           addString pps (Types.toString' uu);
                                           addString pps " ";
                                           addTV pps tv;
                                           addString pps "- ";
                                           printTexpAux level pps texp; addString pps ")")
         | Arrow (d,cod) => 
               (LP 10;
                printTexpAux 30 pps d;
                addBreak pps 0;
                addString pps " -> ";
                printTexpAux 10 pps cod;
                RP 10)
         | Sect (d,cod) => 
               (LP 5;
                printTexpAux 8 pps d;
                addBreak pps 0;
                addString pps " & ";
                printTexpAux 5 pps cod;
                RP 0)
         | Rsect (d,cod) => 
               (LP 5;
                printTexpAux 8 pps d;
                addBreak pps 0;
                addString pps " && ";
                printTexpAux 5 pps cod;
                RP 0)
         | Univ (a, sort, t) => 
               (LP 0;
                addString pps "-all ";
                addIV pps a;
                addString pps " : ";
                printSort pps sort;
                addString pps "- ";
                addBreak pps 0;
                printTexpAux 0 pps t;
                RP 0)
         | Exis (a, sort, t) =>
               if X.isIntSort sort andalso (case t of Tycon(tc, _, []) => TC.toShortString tc = "int" | _ => false) then
                 addString pps "int"
               else
                (LP 20;
                 addString pps "-exists ";
                 addIV pps a;
                 addString pps " : ";
                 printSort pps sort;
                 addString pps "- ";
                 addBreak pps 0;
                 printTexpAux 20 pps t;
                 RP 20)
         | Union (d,cod) => 
               (LP 40;
                printTexpAux 40 pps d;
                addBreak pps 0;
                addString pps " / ";
                printTexpAux 50 pps cod;
                RP 40)
         | Runion (d,cod) => 
               (LP 40;
                printTexpAux 40 pps d;
                addBreak pps 0;
                addString pps " // ";
                printTexpAux 50 pps cod;
                RP 40)
         | Product (texps) => 
               (LP 30;
                case texps of
                    [] => addString pps "unit"
                  | _ => printTexps 40 " * " pps texps;
                addBreak pps 0;
                RP 30)
         | Tycon (tc, record, []) =>   (* don't print parentheses around nullary type constructors *)
                let in
                    addTC pps tc;
                    printIndexRecord pps record
                end
         | Tycon (tc, record, types) =>
                let in
                    LP 50;
                    addTC pps tc;
                    printIndexRecord pps record;
                    printTexpl pps types;
                    RP 50
                end
         | Top =>
               addString pps "top"
         | Bot =>
               addString pps "bot"
         | Conj (prop, A) =>
               (LP 20;
                addString pps "[";
                printProp pps prop;
                addString pps "]";
                addBreak pps 1;
                printTexpAux 20 pps A;
                RP 20)
         | Implies (prop, A) =>
               (LP 0;
                addString pps "{{";
                printProp pps prop;
                addString pps "}}";
                addBreak pps 1;
                printTexpAux 20 pps A;
                RP 0)
         | Record (fld, A) =>
               (LP 0;
                addString pps "{";
                addString pps fld;
                addString pps " : ";
                printTexpAux 1 pps A;
                addString pps "}";
                RP 0)
    end

  and printTexp pps texp = printTexpAux 0 pps texp

  fun printConcContextElem pps elem =
      case elem of
          CC.IndexVar (sym, sort) =>
              (addIV pps sym; 
               addString pps ":";
               addString pps (X.Sort.toString sort))
        | CC.ProgramVar (pv, texp) => 
              (addPV pps pv;
               addString pps " : ";
               printTexp pps texp)
        | CC.TypeVar tv => 
              addTV pps tv
               


  fun printConcContext pps elems =
      sep ",, " printConcContextElem pps elems

  fun  printTyping pps ([], texp) = printTexp pps texp
                                              (* mandatory, so the annotations on projected expressions will be valid SML; this is a hack, since it doesn't work for actual contextual annotations the user wrote *)

  | printTyping pps (ctxt, texp) =
      (printConcContext pps ctxt;
       addString pps " >:> ";
       printTexp pps texp)

  fun printAnno pps anno = case anno of

       AnnotationType.Type A => printTexp pps A

     | AnnotationType.LeftProgramVar (pv, A, anno) =>
           let in
               addPV pps pv;
               addString pps ":";
               printTexp pps A;
               addString pps " >:> ";
               printAnno pps anno
           end

     | AnnotationType.Some (a, sort, anno) =>
           let in
               addIV pps a;
               addString pps ":";
               printSort pps sort;
               addString pps ". ";
               printAnno pps anno
           end


  fun printAnnotation pps annos =
      addList {left="(", right=")", separator= ",, "} printAnno pps annos

  fun printCtxAnno pps typings =
      addList {left="(", right=")", separator= ", "} printTyping pps typings


  fun printTypedecs pps typedecs = 
      let fun aux [] = ()
             | aux [t] = printDatatype pps t ("X","X")
             | aux (t :: typedecs) = 
                   (printDatatype pps t ("X","X");
                    addBreak pps 1;
                    aux typedecs)
      in 
          addNewline pps;
          aux typedecs
      end

  and printTvinfo pps (Tvinfo(tv, variance)) =
      (printTexp pps (Typevar tv);
       addString pps (Variance.toDeclString variance))

  and printDatatypeParams pps tvinfos =
      let in case tvinfos of
                 [] => ()
               | tvinfo :: tvinfos => (printTvinfo pps tvinfo;
                                       addString pps " ";
                                      printDatatypeParams pps tvinfos)
      end
          
  and printDatatype pps (Datatype {tc, builtin, params, sorting, constructors}) (_, _) = 
          let val builtin = builtin
          in
              addNewlines pps 2;
              addString pps "datatype ";
              if builtin then
                  addString pps "(* builtin in target *)"
              else
                  ();
              (*   printTexpl "," pps (map Typevar tvl); *)
              addTC pps tc;
              addBreak pps 1;
              printSorting pps sorting;
              printDatatypeParams pps params;
(*
              beginBlock pps 2;
                printConstructors pps false constructors;
              endBlock pps;
*)
              addNewline pps
          end
  | printDatatype pps (Synonym {tc, tv, params, definition}) (_, _) = 
        (addString pps "type ";
         printDatatypeParams pps (List.map (fn tv => Tvinfo(tv, Variance.Non)) params);
         addTC pps tc;
         addBreak pps 1;
         addString pps "=";
         addBreak pps 1;
         printTexp pps definition)

  and printSpec pps (sort, defaultIndex) =
      (printSort pps sort;
       let in case defaultIndex of
          NONE => ()
        | SOME defaultIndex => (addString pps " = "; printIndexExp 0 pps defaultIndex)
       end)

  and printField pps (fieldname, spec) =
      (addString pps (IndexFieldName.toShortString fieldname ^ ":");
       printSpec pps spec)

  and printFields pps fields =
      addList {left="{", right="}", separator= ", "}
              printField
              pps
              fields

  and printSorting pps sorting = case sorting of
    X.Sorting.None => ()
  | X.Sorting.Nameless spec => (addString pps "with "; printSpec pps spec)
  | X.Sorting.Fields fields =>
       (addString pps "with ";
        printFields pps fields)

  and printConstructors pps bogus [] = ()
    | printConstructors pps bogus (ctor::ctors) = 
          (printConstructor pps bogus ctor; 
           printConstructors pps true ctors)
  
  and printConstructor pps bogus (Constructor {c, nullary, basetype, conjuncts, elaborated_conjuncts, contype}) = 
      let in 
          printConjuncts pps bogus (c, nullary, basetype, contype)
                  (List.map (fn ((pv0, A0), (elab_pv, elab_A0)) =>
                                      let in 
                                          if pv0 <> elab_pv then print "printConstructor: XXX pv mismatch\n" else ();
                                          (elab_pv, A0, elab_A0)
                                      end) (ListPair.zip (conjuncts, elaborated_conjuncts)));
          addNewline pps
      end
  
  and printConjuncts pps bogus cinfo list = case list of
        [] => ()
      | h::t =>
            let in 
                printConjunct pps cinfo h;
                printConjuncts pps true cinfo t
            end               

  and printConjunct pps (cfamily, nullary, basetype, contype) (c, originalA, elabA) = 
      (addPV pps c;
       addString pps ("printConjunct elabA = ");
       printTexp pps elabA;
       addString pps (". ...");
       let in case elabA of
                    Arrow (d, cod) => 
                       (addBreak pps 1;
                        addString pps "of";
                        addBreak pps 1;
                        printTexp pps d)
                  | _ => ()
       end;
       addString pps " (* datacon ";
       addPV pps c;
       addString pps " : ";
       printTexp pps originalA;
       addString pps " (conjunct of ";
       addPV pps cfamily;
       addString pps ")";
       (if nullary then addString pps " (nullary)" else ());
       addString pps " *)")


(* These functions return strings *)

  fun printDecs pps decs =
      let val _ = addNewline pps
       in 
          printDecl pps IRRELEVANT decs;
          ()
       end


  and printDecl pps kind decs = case decs of
      [] => IRRELEVANT
    | [dec] => printDec pps kind dec
    | dec::decs =>
           let val kind' = printDec pps kind dec
           in
               addBreak pps 1;
               printDecl pps kind' decs               
           end
      
  and printDec pps kind (loc, dec) = case dec of
      Dec (pv, kw, locexp) =>
           let val (next, s) =
                   case (kind, kw) of
                       (_, ValKW) => (VAL, "val")
                     | (_, FunKW) => (FUN, "fun")
           in
               addNewline pps;
               addString pps (s ^ " ");
                 addLoc pps loc;
                 addPV pps pv;
               addString pps " = ";
               printLocexpAux 0 pps locexp;
               next
           end

    | Typedec typedecs => 
          (addLoc pps loc;
           printTypedecs pps typedecs;
           addBreak pps 1;
           TYPE)

    | ValType (pv, dectype) =>
           let val _ = addString pps "(* val"
               val _ = addBreak pps 1
               val _ = addPV pps pv
               val _ = addString pps " : "
           in (case dectype of
                Dectype.AGAINST anno => printAnnotation pps anno
              | Dectype.TOPLEVEL_AGAINST texp =>
                    (addString pps "  TOPLEVEL_AGAINST ";
                     addBreak pps 1;
                     printTexp pps texp)
              | Dectype.TOPLEVEL_NOT texp =>
                    (addString pps "  TOPLEVEL_NOT ";
                     addBreak pps 1;
                     printTexp pps texp)
            ; addString pps " *)"
            ; kind)
           end

    | Datacon (c, texp) =>
          let in 
             addNewline pps;
             addString pps "datacon";
             addBreak pps 1;
             addPV pps c;
             addString pps " : ";
             printTexp pps texp;
             kind
          end

    | TyvarVariance (tv, variance) =>
          let in 
            (*addLoc pps loc;
             addBreak pps 1; *)
             addString pps "type";
             addBreak pps 1;
             addTV pps tv;
             addString pps (Variance.toDeclString variance);
             kind
          end

    | TestSubtype (sense, (A, B)) =>
          let in 
            addString pps "test'subtype";
            addBreak pps 1;
            printTexp pps A;
            addString pps (case sense of IsSubtype => " in " 
                                                          | IsNotSubtype => " not in "
                                                          | MutualSubtypes => " = ");
            printTexp pps B;
            addString pps " end";
            kind
          end

(*
    | DatatypeWith (tc, sorting) =>
        let in 
          (*addLoc pps loc;
           addBreak pps 1; *)
           addString pps "datatype";
           addBreak pps 1;
           addTC pps tc;
           addBreak pps 1; addString pps "with"; addBreak pps 1;
           printSorting pps sorting;
           TYPE
        end
*)


  and printLocexp pps (loc, exp) =
      (addLoc pps loc;
       printExpAux 0 pps exp)

  and printExp pps exp = printExpAux 0 pps exp

  and printConst pps (A, string) = case A of
        Types.Tycon(tc, _, []) =>
             let in case TC.toShortString tc of
                 "string" => addString pps ("\"" ^ String.toString string ^ "\"")
               | "char" => addString pps ("#\"" ^ String.toString string ^ "\"")
               | _ => addString pps string
             end
    | Types.Univ (_, _, A0) => printConst pps (A0, string)   (* to handle 0.0, which has type Univ a:dim. real(a) *)
    | A => fail pps ("printConst type is " ^ p printTexp A ^ " (" ^ string ^ ")")
  
  and printLocexpAux level pps (loc, exp) =
      printExpAux level pps exp

  and printExpAux level pps exp =
        let fun LP threshold = if level > threshold then addString pps "(" else ()
            fun RP threshold = if level > threshold then addString pps ")" else ()
        in
            case exp of
                Const c => printConst pps c

              | Var x => addPV pps x
              | Con x => addPV pps x
              | Lvar x => addPV pps x

              | Fn (pv, exp) =>
                    (LP 0;
                     addString pps "fn ";
                         addPV pps pv;
                     addString pps " => ";
                     addBreak pps 0;
                     printLocexpAux 5 pps exp;
                     RP 0)

              | Merge [] => ()

              | Merge [exp1] =>
                    printLocexpAux 20 pps exp1

              | Merge (exp1 :: exps) =>
                    (LP 10;
                     printLocexpAux 20 pps exp1;
                     addString pps ",, ";
                     printExpAux 10 pps (Merge exps);
                     RP 10)
              
              | Case (exp, arms) => 
                    (LP 20;
                     addString pps "case";
                     addBreak pps 1;
                     printLocexpAux 5 pps exp;
                     addBreak pps 1;
                     addString pps "of";
                     addBreak pps 0;
                     beginBlock pps 2;
                       printArms pps arms;  (* uses level 40 *)
                     endBlock pps;
                     RP 20)
              
              | App (exp1,exp2) => 
                    (LP 40;
                     printLocexpAux 40 pps exp1;
                     addString pps " ";
                     printLocexpAux 50 pps exp2;
                     RP 40)

              | RecordExp (fld, exp2) => 
                     (addString pps "{";
                      addString pps fld;
                      addString pps " =";
                      addBreak pps 1;
                      printLocexpAux 0 pps exp2;
                      addString pps "}")

              | Conapp (c, exp2) => 
                    (LP 40;
                     addPV pps (c);
                     addString pps " ";
                     printLocexpAux 50 pps exp2;
                     RP 40) 
              
              | Tuple [] => addString pps "()"
              | Tuple exps => printExps pps exps
              
              | Proj (n, exp) =>
                    (addString pps "#";
                     addString pps n;
                     addString pps "(";
                     printLocexpAux 0 pps exp;
                     addString pps ")")

              | Let (decs, exp) =>
                     let fun print_through (loc, exp) =
                             case exp of
                                 Let(decs, body) => (printDecs pps decs;
                                                     print_through body)
                               | _ => 
                                    (endBlock pps;
                                     addNewline pps;
                                     addString pps "in";
                                     beginBlock pps 4;
                                         printLocexp pps (loc, exp);
                                     endBlock pps;
                                     addString pps "end")
                     in
                         addString pps "let";
                         beginBlock pps 4;
                         printDecs pps decs;
                         print_through exp
                     end

              | Raise exp =>
                     (LP 70;
                      addString pps "raise ";
                      printLocexpAux 80 pps exp;
                      RP 70)
              | Handle (exp1, x, exp2) =>
                     (LP 80;
                      addString pps "try ";
                      printLocexpAux 0 pps exp1;
                      addString pps " handle ";
                      addPV pps x;
                      addString pps " =>";
                      addBreak pps 1;
                      printLocexpAux 10 pps exp2;
                      addString pps "end";
                      RP 80)
               
               | Spy (_, exp) =>
                     (LP 80;
                      addString pps "??";
                      printLocexpAux 100 pps exp;
                      RP 80)
               
               | Leftanno (leftanno, exp) =>
                     (LP 15;
                      printLeftanno pps leftanno;
                      printLocexpAux 20 pps exp;
                      RP 15)
               
               | Anno (locexp, anno) =>
                    (LP 80;
                     printLocexpAux 100 pps locexp;
                     addString pps " : ";
                     printAnnotation pps anno;
                     RP 80)
               | Lethint (anno, locexp) =>
                    (addString pps "hint ";
                     printAnnotation pps anno;
                     addString pps " in ";
                     printLocexp pps locexp;
                     addString pps " end ")
               | LET (pv, locexp, exp) =>
                    (addString pps "(LET "; 
                         addPV pps (pv); addString pps " = ";
                         printLocexp pps locexp;
                         addString pps " IN "; addBreak pps 1;
                         beginBlock pps 4;                
                           printExp pps exp;
                         endBlock pps;
                          addString pps " END)")
               | LETSLACK (pv, locexp, exp) =>
                    (addString pps "LET ~~~";
                         addPV pps pv; addString pps " = ";
                         addBreak pps 1;
                         printLocexp pps locexp;
                         addString pps " IN"; addBreak pps 1;
                         beginBlock pps 4;
                           printExp pps exp;
                         endBlock pps;
                         addString pps "END")
            end

  and printLeftanno pps leftanno = case leftanno of
     LeftProgramVar (x, A) =>
         let in 
             addPV pps x;
             addString pps " : ";
             printTexp pps A;
             addString pps " >:> "
         end

  and printExps pps exps =
      addList {left="(", right=")", separator=", "}
              printLocexp
              pps
              exps

  and printLocexpl pps exps = sep "," printLocexp pps exps

  and printArms pps (arms) =
     (addString pps " ";
      sepLine "|" printArm pps arms)

  and printPat pps pat =
      case pat of
          VarPattern x => addPV pps x
        | WildPattern => addString pps "_ "
        | CtorPattern (c, pat0) => (addPV pps c;
                                    addString pps " ";
                                    case pat0 of
                                        SOME pat0 => 
                                            (addString pps "(";
                                             printPat pps pat0;
                                             addString pps ")")
                                      | NONE => ()) (*addString pps "<nullary>" *)
        | TuplePattern pats =>
              addList {left="(", right=")", separator= ","} printPat pps pats

        | OrPattern [] => addString pps "(_empty_)"        
        | OrPattern pats => addList {left="(", right=")", separator= "|"} printPat pps pats

        | AsPattern (pv, pat0) =>
               (addPV pps pv;
                addString pps " as ";
                printPat pps pat0)
        | StringPattern s => addString pps ("\"" ^ String.toString s ^ "\"")
        | IntPattern i => addString pps (Int.toString i)
  
  and printArm pps (Arm (pat,exp)) =
      (addBreak pps 1;
       printPat pps pat;
       addString pps " =>";
       beginBlock pps 4;
         printLocexpAux 40 pps exp;
       endBlock pps)

  fun printProgram pps (Program (libinfo, decs, exp)) =
      (printDecs pps decs;
       printLocexp pps exp)

  fun print stream program =
      PP.with_pp (toPPConsumer stream) (fn pps => printProgram pps program)

  fun printTargetProgram pps (Program (libinfo, decs, exp)) =
      (printDecs pps decs;
       addString pps "\n\n";
       addString pps "val _ =\n";
       printLocexp pps exp)

  fun printTarget stream program =
      PP.with_pp (toPPConsumer stream) (fn pps => printTargetProgram pps program)



  fun pTexps sep texps = p (printTexps 0 sep) texps

  and pTexpAux _ texp = p (printTexpAux 0) texp

  and pTexp texp = let val result = pTexpAux true texp in result end

  fun pDec d = p (fn pps => fn d => let val _ = printDec pps INITIAL_STATE d in () end) d

  val pConcContextElem = p printConcContextElem
  val pConcContext = p printConcContext

(*
   (* mandatory, so the annotations on projected expressions will be valid SML;
    this is a hack, since it doesn't work for actual contextual annotations the user wrote *)
  fun pTyping ([], texp) = pTexp texp
    | pTyping (ctxt, texp) =
         pConcContext ctxt ^ " |- " ^ pTexp texp
*)
  val pTyping = p printTyping

  val pAnnotation = p printAnnotation
  val pExp = p printExp
  val pLocexp = p printLocexp


end (* structure Print *)
