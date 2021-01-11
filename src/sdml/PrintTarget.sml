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
(*
 * see signature PRINT in Print.sml
 *)

(* PrintTarget: print programs as SML.
 *
 * As Stardust evolves, this setup will likely become unworkable: translating into SML
 * will not be reducible to merely syntactic printing.  We'll probably need a proper target
 * language, close to SML abstract syntax; this module will take *those* programs as input.
 *
 * For the moment, though, the differences are minor enough that the current setup works (more or less).
 *
 * One example of a difference between Print and PrintTarget:
 * Print renders the type of lists at type 'a as
 *
 *           list 'a
 *
 * (StardustML syntax, which plays better with indexed types),
 * but PrintTarget renders the same type as
 *
 *          'a list
 *)

structure PrintTarget :> PRINT = struct
  open Sdml
  open PrintLib
  structure CC = ConcreteContext 
  
  structure X = Indexing
  structure PP = PrettyPrint
  
  datatype deckind = INITIAL_STATE | TYPE | FUN | VAL | IRRELEVANT
  
  type ppstream = PP.ppstream
  type ppconsumer = PP.ppconsumer
  
  val r_printLocs = ref false
  val r_libinfo : Sdml.libinfo option ref = ref NONE
  fun getLibinfo () = Option.valOf (!r_libinfo)

  fun getDistinguished () =
      case getLibinfo() of
          Libinfo {distinguished, ...} => distinguished
  
  val {dprint, ...} =
          Debug.register {full_name= "PrintTarget",
                          short_name= "PrintTarget"}
  
  local
      val index = Option.valOf (Debug.from "PrintTarget")
  in
      fun fail pps s =
          (PP.flush_ppstream pps;
           Debug.makeFail index s)
  end
  
  fun asciify id =
    let val id = String.translate (fn ch =>
                                     let val v = Char.ord ch
                                     in
                                         if v <= 127 then
                                             Char.toString ch
                                         else
                                             "u" ^ Int.toString v
                                     end)
                                  id
    in
        id
    end

  (* For e.g. "::", which would otherwise become the SML-illegal identifier "pv99_::" *)
  fun sanitize id =
    let val id = asciify id
        val id = String.translate (fn #":" => "_"
                                   | ch => Char.toString ch)
                            id
    in
      id
    end
       

  fun addPV pps pv = addString pps (sanitize (PVExtra.toML pv))
  fun addTC pps tc = addString pps ( (*TC.toShortString tc *) TCExtra.toML tc)
  fun addTV pps tv = addString pps ("'a" ^ Int.toString (TV.toInt tv))
  fun addEXTV pps tv = addString pps ("'E" ^ Int.toString (TV.toInt tv))
  fun addIV pps iv = addString pps (IndexSym.toString iv)
  fun addFld pps fld = addString pps (IndexFieldName.toShortString fld)


  val p = PrintLib.p

  fun printSort pps sort =
      (addString pps (X.Sort.toString sort);
       addBreak pps 0)

  fun pSort sort = X.Sort.toString sort

  val printIndexExp = Print.printIndexExp

  fun printProp pps prop = addString pps (X.Constraint.toString prop)

  fun printTexps level delim pps texps =
      sep delim (printTexpAux level) pps texps

  and printTexpl pps [] = ()
    | printTexpl pps [texp] = printTexpAux 60 pps texp
    | printTexpl pps texps =
         addList {left="(", right=")", separator=", "} (printTexpAux 0) pps texps

  and printIndexRecord pps record = Print.printIndexRecord pps record

(* levels:
 0:  -all-  &  { }
10:  ->
20:  -exists-  [ ]
30:  *
40:  \/
50:  type application
60:  inside type argument
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
               (LP 0;
                printTexpAux 0 pps d;
                addBreak pps 0;
                addString pps " & ";
                printTexpAux 0 pps cod;
                RP 0)
         | Rsect (d,cod) => 
               (LP 0;
                printTexpAux 0 pps d;
                addBreak pps 0;
                addString pps " && ";
                printTexpAux 0 pps cod;
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
                printTexpAux 50 pps d;
                addBreak pps 0;
                addString pps " / ";
                printTexpAux 50 pps cod;
                RP 40)
         | Runion (d,cod) => 
               (LP 40;
                printTexpAux 50 pps d;
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
         | Tycon (tc, record, types) =>
                let in
                    LP 50;
                    let in case types of 
                        [] => ()
                      | texps => (printTexpl pps texps;
                                  addBreak pps 1)
                    end; 
                    addTC pps tc;
                    printIndexRecord pps record;
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
               addString pps (Indexing.Sort.toString sort))
        | CC.ProgramVar (pv, texp) => 
              (addPV pps pv;
               addString pps " : ";
               printTexp pps texp)
        | CC.TypeVar tv => 
              addTV pps tv
               


  fun printConcContext pps elems =
      sep ", " printConcContextElem pps elems

  fun  printTyping pps ([], texp) = printTexp pps texp
                                              (* mandatory, so the annotations on projected expressions will be valid SML; this is a hack, since it doesn't work for actual contextual annotations the user wrote *)

  | printTyping pps (ctxt, texp) =
      (printConcContext pps ctxt;
       addString pps " |- ";
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
      let fun aux words [] = ()
             | aux words [t] = printDatatype pps t words
             | aux words (t :: typedecs) = 
                   let val _ = printDatatype pps t words
                       val _ = addBreak pps 1
                       val words = case t of Datatype _ => ("and", "withtype") | Synonym _ => ("and", "and")
                   in
                       aux words typedecs
                   end
      in 
          addNewline pps;
          aux ("datatype", "type") typedecs
      end


  and printTvinfo pps (Tvinfo(tv, variance)) =
      (printTexp pps (Typevar tv);
       addString pps ("(* variance: " ^ Variance.toString variance ^ " *)"))

  and printDatatypeParams pps tvinfos =
      let in case tvinfos of
                 [] => ()
               | [tvinfo] => (printTvinfo pps tvinfo; addString pps " ")
               | tvinfos => (addString pps "(";
                             sep ", " printTvinfo pps tvinfos;
                             addString pps ") ")
      end
          
  and printDatatype pps (Datatype {tc, builtin, params, sorting, constructors}) (datatypeWord, _) = 
      if tc = (#exnTC (getDistinguished ())) then
          printConstructors pps (true(*exn -- print "exception C of ..." instead of "| C of ..."*), false) constructors
      else
          let val builtin = builtin
          in
              if builtin then
                  addString pps "(*-- (don't declare a new bool) "
              else
                  ();
              addString pps datatypeWord;
              addBreak pps 1;
              (*           printTexpl "," pps (map Typevar tvl); *)
              printDatatypeParams pps params;
              addTC pps (tc);
              addBreak pps 1;
              printSorting pps sorting;
              addString pps "=";
              addBreak pps 1;
              beginBlock pps 2;
                addBreak pps 2;  (* extra space to make up for the "| " on the 2nd, 3rd, ... lines *)
                printConstructors pps (false (*not exn*), false (*don't print | before first constructor/conjunct *)) constructors;
              endBlock pps;
              if builtin then
                  addString pps " --*)"
              else
                  ()
          end
  | printDatatype pps (Synonym {tc, tv, params, definition}) (_, typeWord) = 
      (addString pps typeWord;
       addBreak pps 1;
       printDatatypeParams pps (List.map (fn tv => Tvinfo(tv, Variance.Non)) params);
       addTC pps (tc);
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

  and printSorting pps sorting = Print.printSorting pps sorting
  
  and printConstructors pps (isExn, printBar) [] = ()
    | printConstructors pps (isExn, printBar) (ctor::ctors) = 
          (printConstructor pps (isExn, printBar) ctor; 
           printConstructors pps (isExn, true) ctors)
  
  and printConstructor pps (isExn, printBar) (Constructor {c, nullary, basetype, conjuncts, elaborated_conjuncts, contype}) = 
      printConjuncts pps (isExn, printBar) (c, nullary, basetype, contype)
              (List.map (fn ((pv0, A0), (elab_pv, elab_A0)) =>
                                  let in 
                                      if pv0 <> elab_pv then print "printConstructor: XXX pv mismatch\n" else ();
                                      (elab_pv, A0, elab_A0)
                                  end)
                        (ListPair.zip (conjuncts, elaborated_conjuncts)))
  
  and printConjuncts pps (isExn, printBar) cinfo list = case list of
        [] => ()
      | h::t =>
            if isExn then
                let in
                    addNewline pps;
                    addString pps "exception ";
                    printConjunct pps cinfo h;
                    printConjuncts pps (true, true) cinfo t
                end
            else
                let in 
                    if printBar then
                        (addNewline pps;
                         addString pps "| ")
                    else ();
                    printConjunct pps cinfo h;
                    printConjuncts pps (false, true) cinfo t
                end

  and printConjunct pps (cfamily, nullary, basetype, contype) (c, originalA, elabA) = 
      (addPV pps c;
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


  fun printDecs pps decs =
      let val _ = addNewline pps
       in 
          printDecl pps IRRELEVANT decs;
          ()
       end

  and printDecl pps kind decs = case decs of
      [] => VAL  (* doesn't matter *)
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
                     | (FUN, FunKW) => (FUN, "and")
                     | (_, FunKW) => (FUN, "val rec")
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
          (*addLoc pps loc;
           addBreak pps 1; *)
           addString pps "datacon";
           addBreak pps 1;
           addPV pps c;
           addBreak pps 1;
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
           addString pps (Variance.toString variance);
           kind
        end

     | TestSubtype _ =>
           let in 
               ();
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
      let 
           fun LP threshold = if level > threshold then addString pps "(" else ()
           fun RP threshold = if level > threshold then addString pps ")" else ()
      in case exp of
           Const c => printConst pps c
         | Var x => addPV pps x
         | Con x => addPV pps x
         | Lvar x => addPV pps x
         | Case (exp, arms) => 
               (LP 0;
                addString pps "case";
                addBreak pps 1;
                printLocexpAux 5 pps exp;
                addBreak pps 1;
                addString pps "of";
                addBreak pps 0;
                beginBlock pps 2;
                 printArms pps arms;
                endBlock pps;
                RP 0)
         | Fn (pv, exp) =>
               (LP 10;
                addString pps "fn ";
                    addPV pps (pv);
                addString pps " => ";
                addBreak pps 0;
                printLocexpAux 0 pps exp;
                RP 10)
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
                 printLocexpAux 10 pps exp2;
                 addString pps "}")

         | Conapp (c, exp2) => 
                (LP 40;
                 addPV pps c;
                 addString pps " ";
                 printLocexpAux 50 pps exp2;
                 RP 40)
         | Merge exps =>
                 addList {left="(", right=")", separator=",, "}
                          printLocexp
                          pps
                          exps
         | Tuple [] => addString pps "()"
         | Tuple exps =>
               printExps pps exps
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
                (addString pps "raise ";
                 printLocexpAux 10 pps exp)
         | Handle (exp1, x, exp2) =>
                (printLocexpAux 10 pps exp1;
                 addString pps "handle ";
                 addPV pps x;
                 addBreak pps 1;
                 addString pps "=>";
                 addBreak pps 1;
                 printLocexpAux 10 pps exp2)
          | Spy (_, exp) =>
                (addString pps "?? ";
                 printLocexpAux 40 pps exp)
          | Anno (locexp, anno) =>
               (LP 10;
                printLocexpAux 10 pps locexp;
                addString pps " : ";
                printAnnotation pps anno;
                RP 10)
          | Lethint (anno, locexp) =>
               (addString pps "hint ";
                printAnnotation pps anno;
                addString pps " in ";
                printLocexpAux 0 pps locexp;
                addString pps " end ")
          | LET(pv, locexp, exp) =>
               (addString pps "(LET "; 
                    addPV pps (pv); addString pps " = ";
                    printLocexp pps locexp;
                    addString pps " IN "; addBreak pps 1;
                    beginBlock pps 4;
                      printExp pps exp;
                    endBlock pps;
                     addString pps " END)")
(*          | LETDN(pv, locexp, exp) =>
               (addString pps "LETDN "; addBreak pps 1;
                    addPV pps (pv); addString pps " = ";
                    addBreak pps 1;
                    printLocexp pps locexp;
                    addBreak pps 1; addString pps "IN"; addBreak pps 1;
                    beginBlock pps 2;
                      printExp pps exp;
                    endBlock pps;
                    addBreak pps 1; addString pps "END"
                ) *)
          | LETSLACK(pv, locexp, exp) =>
               (addString pps "LET ~~~";
                    addPV pps (pv); addString pps " = ";
                    addBreak pps 1;
                    printLocexp pps locexp;
                    addString pps " IN"; addBreak pps 1;
                    beginBlock pps 4;
                      printExp pps exp;
                    endBlock pps;
                    addString pps "END")
       end

  and printExps pps exps =
      addList {left="(", right=")", separator=", "} printLocexp pps exps

  and printLocexpl pps exps = sep "," printLocexp pps exps

  and printArms pps (arms) =
     (addString pps " ";
      sepLine "|" printArm pps arms)

  and printPat pps pat =
      case pat of
          VarPattern x => addPV pps x
        | WildPattern => (addString pps "_ ")
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
      (r_libinfo := SOME libinfo;
       printDecs pps decs;
       printLocexp pps exp)
        
  fun print stream program =
      PP.with_pp (toPPConsumer stream) (fn pps => printProgram pps program)

  fun printTargetProgram pps (Program (libinfo, decs, exp)) =
      (r_libinfo := SOME libinfo;
       printDecs pps decs;
       addString pps "\n\n";
       addString pps "val _ =\n";
       printLocexp pps exp)

  fun printTarget stream program =
      PP.with_pp (toPPConsumer stream) (fn pps => printTargetProgram pps program)

  fun pTexps sep texps = p (printTexps 0 sep) texps
  and pTexpAux _ texp = p (printTexpAux 0) texp
  and pTexp texp = let val result = pTexpAux 0 texp in result end

  fun pDec d = p (fn pps => fn d => let val _ = printDec pps INITIAL_STATE d in () end) d

  val pConcContextElem = p printConcContextElem
  val pConcContext = p printConcContext
  val pTyping = p printTyping
  val pAnnotation = p printAnnotation
  val pExp = p printExp
  val pLocexp = p printLocexp


end (* structure PrintTarget *)
