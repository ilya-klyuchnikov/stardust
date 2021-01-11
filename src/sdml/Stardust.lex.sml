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
functor SdmlLexFn(structure Tokens : Sdml_TOKENS)  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
A | F | S | INITIAL
    structure UserDeclarations = 
      struct

(* Substantially based on a file from SML/NJ 0.93:

      Copyright 1989 by AT&T Bell Laboratories

  Also see the copyright notice in SMLNJ-LICENSE.
*)

structure TokTable = SdmlTokenTableFn(Tokens);
type svalue = Tokens.svalue
type pos = int
type lexresult = (svalue,pos) Tokens.token
type lexarg = {comLevel : int ref, 
               lineNum : int ref,
               linePos : int list ref, (* offsets of lines in file *)
               charlist : string list ref,
               stringtype : bool ref,
               stringstart : int ref, (* start of current string or comment*)
               argument : (int * int -> string -> unit)
                           * (int -> int -> Location.location )
                           * (int -> int -> Sdml.exp -> Sdml.locexp)
     }
type arg = lexarg
type ('a,'b) token = ('a,'b) Tokens.token
val eof = fn ({comLevel,argument=(err,_,_),linePos,stringstart,stringtype,
               lineNum,charlist}:lexarg) => 
                        let 
                        val pos = Int.max(!stringstart+2, hd(!linePos))
            in if !comLevel>0 then err (!stringstart,pos) "unclosed comment"
                              else ();
               Tokens.EOF(pos,pos)
           end  
fun addString (charlist,s:string) = charlist := s :: (!charlist)
fun makeString charlist = (concat(rev(!charlist)) before charlist := nil)
fun inc x = (x := (!x) + 1; !x)
fun dec x = (x := (!x) - 1; !x)
fun ordof (s,n) = ord (String.sub (s,n))

  (* Note:

<INITIAL>"{" 	=> (Tokens.LBRACE(yypos,yypos+1));
<INITIAL>"}" 	=> (Tokens.RBRACE(yypos,yypos+1));
<INITIAL>"&"    => (Tokens.INTERSECTION(yypos,yypos+1));
<INITIAL>"\\/"    => (Tokens.UNION(yypos,yypos+2));

      Symbols that could be identifiers MUST NOT APPEAR HERE!
      Edit TokenTable.sml instead!
*)



      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
Vector.fromList []
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ({comLevel,lineNum,argument,linePos,charlist,stringstart,stringtype})) () = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inc lineNum; linePos := yypos :: !linePos; continue()))
fun yyAction2 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.SEMICOLON(yypos,yypos+1)))
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.WILD(yypos,yypos+1)))
fun yyAction4 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COMMA(yypos,yypos+1)))
fun yyAction5 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.PERIOD(yypos,yypos+1)))
fun yyAction6 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DBLCOMMA(yypos,yypos+1)))
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LPAREN(yypos,yypos+1)))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RPAREN(yypos,yypos+1)))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LBRACE(yypos,yypos+1)))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RBRACE(yypos,yypos+1)))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DASHALL(yypos,yypos+4)))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DASHEXISTS(yypos,yypos+7)))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LBRACK(yypos,yypos+1)))
fun yyAction14 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RBRACK(yypos,yypos+1)))
fun yyAction15 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.HASH(yypos,yypos+1)))
fun yyAction16 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ASTERISK(yypos,yypos+1)))
fun yyAction17 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ANTICOLON(yypos,yypos+2)))
fun yyAction18 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.PLUS(yypos,yypos+1)))
fun yyAction19 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.MINUS(yypos,yypos+1)))
fun yyAction20 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TURNSTILE(yypos,yypos+2)))
fun yyAction21 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ARROW(yypos,yypos+2)))
fun yyAction22 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DARROW(yypos,yypos+2)))
fun yyAction23 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DQUESTION(yypos,yypos+2)))
fun yyAction24 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LEFTANNO(yypos,yypos+3)))
fun yyAction25 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COLON(yypos,yypos+1)))
fun yyAction26 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DBLCOLON(yypos,yypos+2)))
fun yyAction27 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.TYVAR(yytext,yypos,yypos+size yytext))
      end
fun yyAction28 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (TokTable.checkToken(yytext,yypos))
      end
fun yyAction29 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (TokTable.checkToken(yytext,yypos))
      end
fun yyAction30 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.REAL(yytext,yypos,yypos+size yytext))
      end
fun yyAction31 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT(yytext,yypos,yypos+size yytext))
      end
fun yyAction32 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT(yytext,yypos,yypos+size yytext))
      end
fun yyAction33 (strm, lastMatch : yymatch) = (yystrm := strm;
      (charlist := [""]; stringstart := yypos;
			stringtype := true; YYBEGIN S; continue()))
fun yyAction34 (strm, lastMatch : yymatch) = (yystrm := strm;
      (charlist := [""]; stringstart := yypos;
                    stringtype := false; YYBEGIN S; continue()))
fun yyAction35 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN A; stringstart := yypos; comLevel := 1; continue()))
fun yyAction36 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((#1(argument)) (yypos,yypos+1) "unmatched close comment";
		    continue()))
fun yyAction37 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((#1(argument)) (yypos,yypos) "non-Ascii character";
		    continue()))
fun yyAction38 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((#1(argument)) (yypos,yypos) "illegal token";
		    continue()))
fun yyAction39 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inc comLevel; continue()))
fun yyAction40 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inc lineNum; linePos := yypos :: !linePos; continue()))
fun yyAction41 (strm, lastMatch : yymatch) = (yystrm := strm;
      (dec comLevel; if !comLevel=0 then YYBEGIN INITIAL else (); continue()))
fun yyAction42 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction43 (strm, lastMatch : yymatch) = (yystrm := strm;
      (let val s = makeString charlist
                        val s = if size s <> 1 andalso not(!stringtype)
                                 then ((#1(argument)) (!stringstart,yypos) 
                                      "character constant not length 1"
				       ;substring(s^"x",0,1))
                                 else s
                        val t = (s,!stringstart,yypos+1)
                    in YYBEGIN INITIAL;
                       if !stringtype then Tokens.STRING t else Tokens.CHAR t
                    end))
fun yyAction44 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((#1(argument)) (!stringstart,yypos) "unclosed string";
		    inc lineNum; linePos := yypos :: !linePos;
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos)))
fun yyAction45 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (addString(charlist,yytext); continue())
      end
fun yyAction46 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inc lineNum; linePos := yypos :: !linePos;
		    YYBEGIN F; continue()))
fun yyAction47 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN F; continue()))
fun yyAction48 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inc lineNum; linePos := yypos :: !linePos; continue()))
fun yyAction49 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction50 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN S; stringstart := yypos; continue()))
fun yyAction51 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((#1(argument)) (!stringstart,yypos) "unclosed string";
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos+1)))
fun yyAction52 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist,"\t"); continue()))
fun yyAction53 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist,"\n"); continue()))
fun yyAction54 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist,"\\"); continue()))
fun yyAction55 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist,"\""); continue()))
fun yyAction56 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (addString(charlist,str (chr(ordof(yytext,2)-ord(#"@")))); continue())
      end
fun yyAction57 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (let val x = ordof(yytext,1)*100
	     +ordof(yytext,2)*10
	     +ordof(yytext,3)
	     -(ord(#"0")*111)
  in (if x>255
      then (#1(argument)) (yypos,yypos+4) "illegal ascii escape"
      else addString(charlist,str (chr x));
      continue())
  end)
      end
fun yyAction58 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((#1(argument)) (yypos,yypos+1) "illegal string escape";
		    continue()))
fun yyQ60 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"'"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"'"
                  then if inp = #"%"
                      then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"a"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"_"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"_"
                  then if inp <= #"Z"
                      then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ59 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"'"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"'"
                  then if inp = #"%"
                      then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"a"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"_"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"_"
                  then if inp <= #"Z"
                      then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ65 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction30(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ65(strm', yyMATCH(strm, yyAction30, yyNO_MATCH))
            else if inp < #"0"
              then yyAction30(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ65(strm', yyMATCH(strm, yyAction30, yyNO_MATCH))
              else yyAction30(strm, yyNO_MATCH)
      (* end case *))
fun yyQ66 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ65(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ65(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ64 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #":"
              then yystuck(lastMatch)
            else if inp < #":"
              then if inp <= #"/"
                  then yystuck(lastMatch)
                  else yyQ65(strm', lastMatch)
            else if inp = #"~"
              then yyQ66(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ67 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction30(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"E"
              then yyQ64(strm', yyMATCH(strm, yyAction30, yyNO_MATCH))
            else if inp < #"E"
              then if inp = #"0"
                  then yyQ67(strm', yyMATCH(strm, yyAction30, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction30(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ67(strm', yyMATCH(strm, yyAction30, yyNO_MATCH))
                  else yyAction30(strm, yyNO_MATCH)
            else if inp = #"e"
              then yyQ64(strm', yyMATCH(strm, yyAction30, yyNO_MATCH))
              else yyAction30(strm, yyNO_MATCH)
      (* end case *))
fun yyQ63 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ67(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ67(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ62 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction32(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction32(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"/"
                  then yyAction32(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ63(strm', yyMATCH(strm, yyAction32, yyNO_MATCH))
                      else yyAction32(strm, yyNO_MATCH)
                  else yyQ62(strm', yyMATCH(strm, yyAction32, yyNO_MATCH))
            else if inp = #"F"
              then yyAction32(strm, yyNO_MATCH)
            else if inp < #"F"
              then if inp = #"E"
                  then yyQ64(strm', yyMATCH(strm, yyAction32, yyNO_MATCH))
                  else yyAction32(strm, yyNO_MATCH)
            else if inp = #"e"
              then yyQ64(strm', yyMATCH(strm, yyAction32, yyNO_MATCH))
              else yyAction32(strm, yyNO_MATCH)
      (* end case *))
fun yyQ61 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ58 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyQ62(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"?"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ57 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ68 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction20(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction20(strm, yyNO_MATCH)
      (* end case *))
fun yyQ56 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"?"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"?"
              then if inp = #"."
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"."
                  then if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"'"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"'"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp = #"-"
                      then yyQ68(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #":"
                  then if inp = #"/"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"A"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"A"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ55 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction9(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction9(strm, yyNO_MATCH)
      (* end case *))
fun yyQ71 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"<"
              then if inp = #","
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp = #"#"
                      then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp < #"#"
                      then if inp = #"!"
                          then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                          else yyAction28(strm, yyNO_MATCH)
                    else if inp = #"'"
                      then yyAction28(strm, yyNO_MATCH)
                    else if inp < #"'"
                      then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp <= #")"
                      then yyAction28(strm, yyNO_MATCH)
                      else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"0"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"0"
                  then if inp = #"."
                      then yyAction28(strm, yyNO_MATCH)
                      else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #":"
                  then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"a"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #"a"
              then if inp = #"]"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"A"
                      then yyAction28(strm, yyNO_MATCH)
                    else if inp < #"A"
                      then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp = #"\\"
                      then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                else if inp = #"_"
                  then yyAction28(strm, yyNO_MATCH)
                  else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp = #"~"
              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ72 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"<"
              then if inp = #"*"
                  then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"*"
                  then if inp = #"%"
                      then yyQ72(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp < #"%"
                      then if inp = #"\""
                          then yyAction28(strm, yyNO_MATCH)
                        else if inp < #"\""
                          then if inp = #"!"
                              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                              else yyAction28(strm, yyNO_MATCH)
                          else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp = #"'"
                      then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp = #"&"
                      then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                else if inp = #"/"
                  then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"-"
                      then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                    else if inp < #"-"
                      then if inp = #","
                          then yyAction28(strm, yyNO_MATCH)
                          else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #";"
                  then yyAction28(strm, yyNO_MATCH)
                  else yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp = #"a"
              then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"]"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"["
                      then yyAction28(strm, yyNO_MATCH)
                    else if inp < #"["
                      then if inp <= #"@"
                          then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                          else yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp = #"~"
              then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ71(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp < #"|"
                  then if inp = #"{"
                      then yyAction28(strm, yyNO_MATCH)
                      else yyQ60(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ72(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ72(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ70 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ71(strm', lastMatch)
            else if inp < #"<"
              then if inp = #"*"
                  then yyQ71(strm', lastMatch)
                else if inp < #"*"
                  then if inp = #"%"
                      then yyQ72(strm', lastMatch)
                    else if inp < #"%"
                      then if inp = #"\""
                          then yystuck(lastMatch)
                        else if inp < #"\""
                          then if inp = #"!"
                              then yyQ71(strm', lastMatch)
                              else yystuck(lastMatch)
                          else yyQ71(strm', lastMatch)
                    else if inp = #"'"
                      then yyQ60(strm', lastMatch)
                    else if inp = #"&"
                      then yyQ71(strm', lastMatch)
                      else yystuck(lastMatch)
                else if inp = #"/"
                  then yyQ71(strm', lastMatch)
                else if inp < #"/"
                  then if inp = #"-"
                      then yyQ71(strm', lastMatch)
                    else if inp < #"-"
                      then if inp = #","
                          then yystuck(lastMatch)
                          else yyQ71(strm', lastMatch)
                      else yystuck(lastMatch)
                else if inp = #":"
                  then yyQ71(strm', lastMatch)
                else if inp = #";"
                  then yystuck(lastMatch)
                  else yyQ60(strm', lastMatch)
            else if inp = #"a"
              then yyQ60(strm', lastMatch)
            else if inp < #"a"
              then if inp = #"]"
                  then yystuck(lastMatch)
                else if inp < #"]"
                  then if inp = #"["
                      then yystuck(lastMatch)
                    else if inp < #"["
                      then if inp <= #"@"
                          then yyQ71(strm', lastMatch)
                          else yyQ60(strm', lastMatch)
                      else yyQ71(strm', lastMatch)
                else if inp = #"_"
                  then yyQ60(strm', lastMatch)
                  else yyQ71(strm', lastMatch)
            else if inp = #"~"
              then yyQ71(strm', lastMatch)
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ71(strm', lastMatch)
                else if inp < #"|"
                  then if inp = #"{"
                      then yystuck(lastMatch)
                      else yyQ60(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"\128"
              then yyQ72(strm', lastMatch)
            else if inp < #"\128"
              then yystuck(lastMatch)
            else if inp <= #"\255"
              then yyQ72(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ69 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"("
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"&"
                      then yyAction28(strm, yyNO_MATCH)
                    else if inp < #"&"
                      then if inp = #"%"
                          then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                          else yyAction28(strm, yyNO_MATCH)
                      else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"/"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ70(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                  else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp = #"`"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"["
                  then if inp <= #"@"
                      then yyAction28(strm, yyNO_MATCH)
                      else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ54 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"("
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"&"
                      then yyAction28(strm, yyNO_MATCH)
                    else if inp < #"&"
                      then if inp = #"%"
                          then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                          else yyAction28(strm, yyNO_MATCH)
                      else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"/"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ70(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                  else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp = #"`"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"["
                  then if inp <= #"@"
                      then yyAction28(strm, yyNO_MATCH)
                      else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ53 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ52 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ51 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ50 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"("
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"&"
                      then yyAction28(strm, yyNO_MATCH)
                    else if inp < #"&"
                      then if inp = #"%"
                          then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                          else yyAction28(strm, yyNO_MATCH)
                      else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"/"
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ70(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                      else yyAction28(strm, yyNO_MATCH)
                  else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp = #"`"
              then yyAction28(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction28(strm, yyNO_MATCH)
                else if inp < #"["
                  then if inp <= #"@"
                      then yyAction28(strm, yyNO_MATCH)
                      else yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
                  else yyAction28(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ69(strm', yyMATCH(strm, yyAction28, yyNO_MATCH))
              else yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ73 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction23(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction23(strm, yyNO_MATCH)
      (* end case *))
fun yyQ49 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"?"
              then yyQ73(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
              else yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ75 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction24(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction24(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                          else yyAction24(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction24(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                      else yyAction24(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction24(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                      else yyAction24(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction24(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction24(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                      else yyAction24(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                  else yyAction24(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction24(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
                  else yyAction24(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
              else yyAction24(strm, yyNO_MATCH)
      (* end case *))
fun yyQ74 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"0"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"0"
                  then if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"'"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"'"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp = #"/"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"<"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #">"
                  then yyQ75(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"?"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ48 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ74(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ76 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction22(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction22(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                          else yyAction22(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction22(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                      else yyAction22(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction22(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                      else yyAction22(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction22(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction22(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                      else yyAction22(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                  else yyAction22(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction22(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                  else yyAction22(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
              else yyAction22(strm, yyNO_MATCH)
      (* end case *))
fun yyQ47 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"0"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"0"
                  then if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"'"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"'"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp = #"/"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"<"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #">"
                  then yyQ76(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"?"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ46 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ78 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction26(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction26(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                          else yyAction26(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction26(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                      else yyAction26(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction26(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                      else yyAction26(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction26(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction26(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                      else yyAction26(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                  else yyAction26(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction26(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
                  else yyAction26(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction26, yyNO_MATCH))
              else yyAction26(strm, yyNO_MATCH)
      (* end case *))
fun yyQ77 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction17(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                          else yyAction17(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction17(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ45 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction25(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction25(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ77(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                          else yyAction25(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction25(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                      else yyAction25(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction25(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ78(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                      else yyAction25(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction25(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction25(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                      else yyAction25(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                  else yyAction25(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction25(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
                  else yyAction25(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction25, yyNO_MATCH))
              else yyAction25(strm, yyNO_MATCH)
      (* end case *))
fun yyQ79 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction31(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"/"
                  then yyAction31(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ63(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
                      else yyAction31(strm, yyNO_MATCH)
                  else yyQ79(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
            else if inp = #"F"
              then yyAction31(strm, yyNO_MATCH)
            else if inp < #"F"
              then if inp = #"E"
                  then yyQ64(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
                  else yyAction31(strm, yyNO_MATCH)
            else if inp = #"e"
              then yyQ64(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
              else yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ44 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction31(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"/"
                  then yyAction31(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ63(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
                      else yyAction31(strm, yyNO_MATCH)
                  else yyQ79(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
            else if inp = #"F"
              then yyAction31(strm, yyNO_MATCH)
            else if inp < #"F"
              then if inp = #"E"
                  then yyQ64(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
                  else yyAction31(strm, yyNO_MATCH)
            else if inp = #"e"
              then yyQ64(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
              else yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ43 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction5(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction5(strm, yyNO_MATCH)
      (* end case *))
fun yyQ87 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction12(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction12(strm, yyNO_MATCH)
      (* end case *))
fun yyQ86 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"s"
              then yyQ87(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ85 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"t"
              then yyQ86(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ84 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"s"
              then yyQ85(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ83 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"i"
              then yyQ84(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ82 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"x"
              then yyQ83(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ89 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction11(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction11(strm, yyNO_MATCH)
      (* end case *))
fun yyQ88 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"l"
              then yyQ89(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ81 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"l"
              then yyQ88(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ80 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction21(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction21(strm, yyNO_MATCH)
      (* end case *))
fun yyQ42 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ81(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #">"
                  then yyQ80(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyAction19(strm, yyNO_MATCH)
            else if inp = #"e"
              then yyQ82(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
              else yyAction19(strm, yyNO_MATCH)
      (* end case *))
fun yyQ90 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ41 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #","
              then yyQ90(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ40 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction18(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction18(strm, yyNO_MATCH)
      (* end case *))
fun yyQ91 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ39 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction16(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #")"
              then yyQ91(strm', yyMATCH(strm, yyAction16, yyNO_MATCH))
              else yyAction16(strm, yyNO_MATCH)
      (* end case *))
fun yyQ38 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction8(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction8(strm, yyNO_MATCH)
      (* end case *))
fun yyQ92 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction35(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction35(strm, yyNO_MATCH)
      (* end case *))
fun yyQ37 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction7(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ92(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
              else yyAction7(strm, yyNO_MATCH)
      (* end case *))
fun yyQ97 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"'"
                  then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp < #"'"
                  then if inp = #"%"
                      then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyAction27(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction27(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp = #"a"
              then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp < #"_"
                  then if inp <= #"Z"
                      then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyAction27(strm, yyNO_MATCH)
                  else yyAction27(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
              else yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ99 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"<"
              then if inp = #","
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp = #"#"
                      then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp < #"#"
                      then if inp = #"!"
                          then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                          else yyAction27(strm, yyNO_MATCH)
                    else if inp = #"'"
                      then yyAction27(strm, yyNO_MATCH)
                    else if inp < #"'"
                      then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp <= #")"
                      then yyAction27(strm, yyNO_MATCH)
                      else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp = #"0"
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #"0"
                  then if inp = #"."
                      then yyAction27(strm, yyNO_MATCH)
                      else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp = #":"
                  then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp = #"a"
              then yyAction27(strm, yyNO_MATCH)
            else if inp < #"a"
              then if inp = #"]"
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"A"
                      then yyAction27(strm, yyNO_MATCH)
                    else if inp < #"A"
                      then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp = #"\\"
                      then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyAction27(strm, yyNO_MATCH)
                else if inp = #"_"
                  then yyAction27(strm, yyNO_MATCH)
                  else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp = #"~"
              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"\128"
              then yyAction27(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
              else yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ100 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"<"
              then if inp = #"*"
                  then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp < #"*"
                  then if inp = #"%"
                      then yyQ100(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp < #"%"
                      then if inp = #"\""
                          then yyAction27(strm, yyNO_MATCH)
                        else if inp < #"\""
                          then if inp = #"!"
                              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                              else yyAction27(strm, yyNO_MATCH)
                          else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp = #"'"
                      then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp = #"&"
                      then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyAction27(strm, yyNO_MATCH)
                else if inp = #"/"
                  then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"-"
                      then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                    else if inp < #"-"
                      then if inp = #","
                          then yyAction27(strm, yyNO_MATCH)
                          else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyAction27(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp = #";"
                  then yyAction27(strm, yyNO_MATCH)
                  else yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp = #"a"
              then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"]"
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"["
                      then yyAction27(strm, yyNO_MATCH)
                    else if inp < #"["
                      then if inp <= #"@"
                          then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                          else yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp = #"~"
              then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ99(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp < #"|"
                  then if inp = #"{"
                      then yyAction27(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ100(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"\128"
              then yyAction27(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ100(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
              else yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ98 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ99(strm', lastMatch)
            else if inp < #"<"
              then if inp = #"*"
                  then yyQ99(strm', lastMatch)
                else if inp < #"*"
                  then if inp = #"%"
                      then yyQ100(strm', lastMatch)
                    else if inp < #"%"
                      then if inp = #"\""
                          then yystuck(lastMatch)
                        else if inp < #"\""
                          then if inp = #"!"
                              then yyQ99(strm', lastMatch)
                              else yystuck(lastMatch)
                          else yyQ99(strm', lastMatch)
                    else if inp = #"'"
                      then yyQ97(strm', lastMatch)
                    else if inp = #"&"
                      then yyQ99(strm', lastMatch)
                      else yystuck(lastMatch)
                else if inp = #"/"
                  then yyQ99(strm', lastMatch)
                else if inp < #"/"
                  then if inp = #"-"
                      then yyQ99(strm', lastMatch)
                    else if inp < #"-"
                      then if inp = #","
                          then yystuck(lastMatch)
                          else yyQ99(strm', lastMatch)
                      else yystuck(lastMatch)
                else if inp = #":"
                  then yyQ99(strm', lastMatch)
                else if inp = #";"
                  then yystuck(lastMatch)
                  else yyQ97(strm', lastMatch)
            else if inp = #"a"
              then yyQ97(strm', lastMatch)
            else if inp < #"a"
              then if inp = #"]"
                  then yystuck(lastMatch)
                else if inp < #"]"
                  then if inp = #"["
                      then yystuck(lastMatch)
                    else if inp < #"["
                      then if inp <= #"@"
                          then yyQ99(strm', lastMatch)
                          else yyQ97(strm', lastMatch)
                      else yyQ99(strm', lastMatch)
                else if inp = #"_"
                  then yyQ97(strm', lastMatch)
                  else yyQ99(strm', lastMatch)
            else if inp = #"~"
              then yyQ99(strm', lastMatch)
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ99(strm', lastMatch)
                else if inp < #"|"
                  then if inp = #"{"
                      then yystuck(lastMatch)
                      else yyQ97(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"\128"
              then yyQ100(strm', lastMatch)
            else if inp < #"\128"
              then yystuck(lastMatch)
            else if inp <= #"\255"
              then yyQ100(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ95 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction27(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"("
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"&"
                      then yyAction27(strm, yyNO_MATCH)
                    else if inp < #"&"
                      then if inp = #"%"
                          then yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                          else yyAction27(strm, yyNO_MATCH)
                      else yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp = #"/"
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #"/"
                  then if inp = #"."
                      then yyQ98(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                      else yyAction27(strm, yyNO_MATCH)
                  else yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp = #"`"
              then yyAction27(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction27(strm, yyNO_MATCH)
                else if inp < #"["
                  then if inp <= #"@"
                      then yyAction27(strm, yyNO_MATCH)
                      else yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
                  else yyAction27(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ95(strm', yyMATCH(strm, yyAction27, yyNO_MATCH))
              else yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ96 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ95(strm', lastMatch)
            else if inp < #"a"
              then if inp = #"A"
                  then yyQ95(strm', lastMatch)
                else if inp < #"A"
                  then yystuck(lastMatch)
                else if inp <= #"Z"
                  then yyQ95(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"\128"
              then yyQ97(strm', lastMatch)
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ95(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp <= #"\255"
              then yyQ97(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ94 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"["
              then yystuck(lastMatch)
            else if inp < #"["
              then if inp = #":"
                  then yystuck(lastMatch)
                else if inp < #":"
                  then if inp <= #"/"
                      then yystuck(lastMatch)
                      else yyQ94(strm', lastMatch)
                else if inp <= #"@"
                  then yystuck(lastMatch)
                  else yyQ95(strm', lastMatch)
            else if inp = #"{"
              then yystuck(lastMatch)
            else if inp < #"{"
              then if inp <= #"`"
                  then yystuck(lastMatch)
                  else yyQ95(strm', lastMatch)
            else if inp = #"\128"
              then yyQ97(strm', lastMatch)
            else if inp < #"\128"
              then yystuck(lastMatch)
            else if inp <= #"\255"
              then yyQ97(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ93 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ96(strm', lastMatch)
            else if inp < #"_"
              then if inp = #":"
                  then yystuck(lastMatch)
                else if inp < #":"
                  then if inp <= #"/"
                      then yystuck(lastMatch)
                      else yyQ94(strm', lastMatch)
                else if inp = #"A"
                  then yyQ95(strm', lastMatch)
                else if inp < #"A"
                  then yystuck(lastMatch)
                else if inp <= #"Z"
                  then yyQ95(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"{"
              then yystuck(lastMatch)
            else if inp < #"{"
              then if inp = #"`"
                  then yystuck(lastMatch)
                  else yyQ95(strm', lastMatch)
            else if inp = #"\128"
              then yyQ97(strm', lastMatch)
            else if inp < #"\128"
              then yystuck(lastMatch)
            else if inp <= #"\255"
              then yyQ97(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ36 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction38(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #"0"
                  then yyQ94(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ93(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
                      else yyAction38(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction38(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ94(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction38(strm, yyNO_MATCH)
                  else yyQ95(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
            else if inp = #"a"
              then yyQ95(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"_"
                  then yyQ96(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
                  else yyAction38(strm, yyNO_MATCH)
            else if inp = #"\128"
              then yyQ97(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
            else if inp < #"\128"
              then if inp <= #"z"
                  then yyQ95(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
                  else yyAction38(strm, yyNO_MATCH)
            else if inp <= #"\255"
              then yyQ97(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
              else yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ101 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction34(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction34(strm, yyNO_MATCH)
      (* end case *))
fun yyQ35 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\""
              then yyQ101(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
              else yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ34 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction33(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction33(strm, yyNO_MATCH)
      (* end case *))
fun yyQ33 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"/"
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp = #"$"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                    else if inp < #"$"
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp <= #"&"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #";"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"?"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"`"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"^"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"}"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"}"
              then if inp = #"|"
                  then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyAction29(strm, yyNO_MATCH)
            else if inp = #"~"
              then yyQ61(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ32 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ102 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\f"
              then yyQ102(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp < #"\f"
              then if inp = #"\t"
                  then yyQ102(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyAction0(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ102(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
              else yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ31 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\f"
              then yyQ102(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp < #"\f"
              then if inp = #"\t"
                  then yyQ102(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyAction0(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ102(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
              else yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ30 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ3 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #";"
              then yyQ46(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp < #";"
              then if inp = #"'"
                  then yyQ36(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp < #"'"
                  then if inp = #"\r"
                      then yyQ30(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp < #"\r"
                      then if inp = #"\n"
                          then yyQ32(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                        else if inp < #"\n"
                          then if inp = #"\t"
                              then yyQ31(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                              else yyQ30(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                        else if inp = #"\v"
                          then yyQ30(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                          else yyQ31(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp = #"\""
                      then yyQ34(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp < #"\""
                      then if inp = #" "
                          then yyQ31(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                        else if inp = #"!"
                          then yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                          else yyQ30(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp = #"#"
                      then yyQ35(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                      else yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ42(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp < #"-"
                  then if inp = #"*"
                      then yyQ39(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp < #"*"
                      then if inp = #"("
                          then yyQ37(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                          else yyQ38(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp = #"+"
                      then yyQ40(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                      else yyQ41(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #"0"
                  then yyQ44(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"."
                      then yyQ43(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                      else yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #":"
                  then yyQ45(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyQ44(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp = #"`"
              then yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ50(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #">"
                      then yyQ48(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp < #">"
                      then if inp = #"<"
                          then yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                          else yyQ47(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp = #"?"
                      then yyQ49(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                      else yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #"]"
                  then yyQ52(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp < #"]"
                  then if inp = #"["
                      then yyQ51(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                    else if inp = #"\\"
                      then yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                      else yyQ50(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #"^"
                  then yyQ33(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyQ53(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp = #"}"
              then yyQ57(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp < #"}"
              then if inp = #"i"
                  then yyQ50(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp < #"i"
                  then if inp = #"h"
                      then yyQ54(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                      else yyQ50(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #"{"
                  then yyQ55(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if inp = #"|"
                  then yyQ56(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp = #"\128"
              then yyQ59(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp < #"\128"
              then if inp = #"~"
                  then yyQ58(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                  else yyQ30(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp <= #"\255"
              then yyQ59(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
              else yyQ30(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
      (* end case *))
fun yyQ26 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction52(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction52(strm, yyNO_MATCH)
      (* end case *))
fun yyQ25 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction53(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction53(strm, yyNO_MATCH)
      (* end case *))
fun yyQ27 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction56(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction56(strm, yyNO_MATCH)
      (* end case *))
fun yyQ24 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ27(strm', lastMatch)
            else if inp < #"@"
              then yystuck(lastMatch)
            else if inp <= #"_"
              then yyQ27(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ23 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction54(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction54(strm, yyNO_MATCH)
      (* end case *))
fun yyQ29 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction57(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction57(strm, yyNO_MATCH)
      (* end case *))
fun yyQ28 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ29(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ29(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ22 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ28(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ28(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ21 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction55(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction55(strm, yyNO_MATCH)
      (* end case *))
fun yyQ20 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction46(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction46(strm, yyNO_MATCH)
      (* end case *))
fun yyQ19 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction47(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction47(strm, yyNO_MATCH)
      (* end case *))
fun yyQ18 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction58(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction58(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #" "
                  then yyQ19(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                else if inp < #" "
                  then if inp = #"\n"
                      then yyQ20(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                    else if inp < #"\n"
                      then if inp = #"\t"
                          then yyQ19(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                          else yyAction58(strm, yyNO_MATCH)
                      else yyAction58(strm, yyNO_MATCH)
                else if inp = #"#"
                  then yyAction58(strm, yyNO_MATCH)
                else if inp < #"#"
                  then if inp = #"!"
                      then yyAction58(strm, yyNO_MATCH)
                      else yyQ21(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                else if inp <= #"/"
                  then yyAction58(strm, yyNO_MATCH)
                  else yyQ22(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
            else if inp = #"_"
              then yyAction58(strm, yyNO_MATCH)
            else if inp < #"_"
              then if inp = #"]"
                  then yyAction58(strm, yyNO_MATCH)
                else if inp < #"]"
                  then if inp = #"\\"
                      then yyQ23(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                      else yyAction58(strm, yyNO_MATCH)
                  else yyQ24(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
            else if inp = #"o"
              then yyAction58(strm, yyNO_MATCH)
            else if inp < #"o"
              then if inp = #"n"
                  then yyQ25(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                  else yyAction58(strm, yyNO_MATCH)
            else if inp = #"t"
              then yyQ26(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
              else yyAction58(strm, yyNO_MATCH)
      (* end case *))
fun yyQ17 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction43(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction43(strm, yyNO_MATCH)
      (* end case *))
fun yyQ16 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction44(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction44(strm, yyNO_MATCH)
      (* end case *))
fun yyQ15 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction45(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\""
              then yyAction45(strm, yyNO_MATCH)
            else if inp < #"\""
              then if inp = #"\n"
                  then yyAction45(strm, yyNO_MATCH)
                  else yyQ15(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
            else if inp = #"\\"
              then yyAction45(strm, yyNO_MATCH)
              else yyQ15(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
      (* end case *))
fun yyQ2 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yyAction45(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\""
              then yyQ17(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
            else if inp < #"\""
              then if inp = #"\n"
                  then yyQ16(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
                  else yyQ15(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
            else if inp = #"\\"
              then yyQ18(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
              else yyQ15(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
      (* end case *))
fun yyQ13 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction50(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction50(strm, yyNO_MATCH)
      (* end case *))
fun yyQ12 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ14 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction49(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\f"
              then yyQ14(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp < #"\f"
              then if inp = #"\t"
                  then yyQ14(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                  else yyAction49(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ14(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
              else yyAction49(strm, yyNO_MATCH)
      (* end case *))
fun yyQ11 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction49(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\f"
              then yyQ14(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp < #"\f"
              then if inp = #"\t"
                  then yyQ14(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                  else yyAction49(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ14(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
              else yyAction49(strm, yyNO_MATCH)
      (* end case *))
fun yyQ10 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction51(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction51(strm, yyNO_MATCH)
      (* end case *))
fun yyQ1 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yyAction49(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\r"
              then yyQ10(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp < #"\r"
              then if inp = #"\n"
                  then yyQ12(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                else if inp < #"\n"
                  then if inp = #"\t"
                      then yyQ11(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                      else yyQ10(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                else if inp = #"\v"
                  then yyQ10(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                  else yyQ11(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp = #"!"
              then yyQ10(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp < #"!"
              then if inp = #" "
                  then yyQ11(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                  else yyQ10(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp = #"\\"
              then yyQ13(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
              else yyQ10(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
      (* end case *))
fun yyQ8 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction41(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction41(strm, yyNO_MATCH)
      (* end case *))
fun yyQ7 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction42(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #")"
              then yyQ8(strm', yyMATCH(strm, yyAction42, yyNO_MATCH))
              else yyAction42(strm, yyNO_MATCH)
      (* end case *))
fun yyQ9 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction39(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction39(strm, yyNO_MATCH)
      (* end case *))
fun yyQ6 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction42(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ9(strm', yyMATCH(strm, yyAction42, yyNO_MATCH))
              else yyAction42(strm, yyNO_MATCH)
      (* end case *))
fun yyQ5 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ4 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction42(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction42(strm, yyNO_MATCH)
      (* end case *))
fun yyQ0 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"("
              then yyQ6(strm', lastMatch)
            else if inp < #"("
              then if inp = #"\n"
                  then yyQ5(strm', lastMatch)
                  else yyQ4(strm', lastMatch)
            else if inp = #"*"
              then yyQ7(strm', lastMatch)
              else yyQ4(strm', lastMatch)
      (* end case *))
in
  (case (!(yyss))
   of A => yyQ0(!(yystrm), yyNO_MATCH)
    | F => yyQ1(!(yystrm), yyNO_MATCH)
    | S => yyQ2(!(yystrm), yyNO_MATCH)
    | INITIAL => yyQ3(!(yystrm), yyNO_MATCH)
  (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
