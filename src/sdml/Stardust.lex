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

%% 
%reject
%s A S F; 
%header (functor SdmlLexFn(structure Tokens : Sdml_TOKENS));
%arg ({comLevel,lineNum,argument,linePos,charlist,stringstart,stringtype});
idchars=[A-Za-z'_0-9\128-\255%];
symbolidchars=[-!%&$#+/:<=>?@\\~`|*\128-\255^];
symbol={symbolidchars}+;
id=[A-Za-z\128-\255]{idchars}*|[A-Za-z]{idchars}*"."{idchars}+|[A-Za-z]{idchars}*"."{symbol};
ws=("\012"|[\t\ ])*;
sym=[!%&$/:<=>@~|`]|\\|\^;
num=[0-9]+;
frac="."{num};
exp=[Ee](~?){num};
real=(~?)(({num}{frac}?{exp})|({num}{frac}{exp}?));
hexnum=[0-9a-fA-F]+;
%%
<INITIAL>{ws}	=> (continue());
<INITIAL>\n	=> (inc lineNum; linePos := yypos :: !linePos; continue());
<INITIAL>";"    => (Tokens.SEMICOLON(yypos,yypos+1));
<INITIAL>"_"    => (Tokens.WILD(yypos,yypos+1));
<INITIAL>","	=> (Tokens.COMMA(yypos,yypos+1));
<INITIAL>"."	=> (Tokens.PERIOD(yypos,yypos+1));
<INITIAL>",,"	=> (Tokens.DBLCOMMA(yypos,yypos+1));
<INITIAL>"("	=> (Tokens.LPAREN(yypos,yypos+1));
<INITIAL>")"	=> (Tokens.RPAREN(yypos,yypos+1));

<INITIAL>"{" 	=> (Tokens.LBRACE(yypos,yypos+1));
<INITIAL>"}" 	=> (Tokens.RBRACE(yypos,yypos+1));

<INITIAL>"-all"	=> (Tokens.DASHALL(yypos,yypos+4));
<INITIAL>"-exists"	=> (Tokens.DASHEXISTS(yypos,yypos+7));
<INITIAL>"["	=> (Tokens.LBRACK(yypos,yypos+1));
<INITIAL>"]"	=> (Tokens.RBRACK(yypos,yypos+1));

<INITIAL>"#"    => (Tokens.HASH(yypos,yypos+1));

<INITIAL>"*"    => (Tokens.ASTERISK(yypos,yypos+1));
<INITIAL>":!"    => (Tokens.ANTICOLON(yypos,yypos+2));
<INITIAL>"+"    => (Tokens.PLUS(yypos,yypos+1));
<INITIAL>"-"    => (Tokens.MINUS(yypos,yypos+1));
<INITIAL>"|-"    => (Tokens.TURNSTILE(yypos,yypos+2));
<INITIAL>"->"    => (Tokens.ARROW(yypos,yypos+2));
<INITIAL>"=>"    => (Tokens.DARROW(yypos,yypos+2));
<INITIAL>"??"    => (Tokens.DQUESTION(yypos,yypos+2));

<INITIAL>">:>"    => (Tokens.LEFTANNO(yypos,yypos+3));

<INITIAL>":"    => (Tokens.COLON(yypos,yypos+1));
<INITIAL>"::"    => (Tokens.DBLCOLON(yypos,yypos+2));
<INITIAL>"'"("'"?)("_"|{num})?{id}
			=> (Tokens.TYVAR(yytext,yypos,yypos+size yytext));
<INITIAL>{id}	        => (TokTable.checkToken(yytext,yypos));
<INITIAL>{sym}+         => (TokTable.checkToken(yytext,yypos));
<INITIAL>{real} => (Tokens.REAL(yytext,yypos,yypos+size yytext));
<INITIAL>{num}	=> (Tokens.INT(yytext,yypos,yypos+size yytext));
<INITIAL>~{num}	=> (Tokens.INT(yytext,yypos,yypos+size yytext));
<INITIAL>\"	=> (charlist := [""]; stringstart := yypos;
			stringtype := true; YYBEGIN S; continue());
<INITIAL>\#\"	=> (charlist := [""]; stringstart := yypos;
                    stringtype := false; YYBEGIN S; continue());
<INITIAL>"(*"	=> (YYBEGIN A; stringstart := yypos; comLevel := 1; continue());
<INITIAL>"*)"	=> ((#1(argument)) (yypos,yypos+1) "unmatched close comment";
		    continue());
<INITIAL>\h	=> ((#1(argument)) (yypos,yypos) "non-Ascii character";
		    continue());
<INITIAL>.	=> ((#1(argument)) (yypos,yypos) "illegal token";
		    continue());

<A>"(*"		=> (inc comLevel; continue());
<A>\n		=> (inc lineNum; linePos := yypos :: !linePos; continue());
<A>"*)"         => (dec comLevel; if !comLevel=0 then YYBEGIN INITIAL else (); continue());
<A>.		=> (continue());
<S>\"	        => (let val s = makeString charlist
                        val s = if size s <> 1 andalso not(!stringtype)
                                 then ((#1(argument)) (!stringstart,yypos) 
                                      "character constant not length 1"
				       ;substring(s^"x",0,1))
                                 else s
                        val t = (s,!stringstart,yypos+1)
                    in YYBEGIN INITIAL;
                       if !stringtype then Tokens.STRING t else Tokens.CHAR t
                    end);
<S>\n		=> ((#1(argument)) (!stringstart,yypos) "unclosed string";
		    inc lineNum; linePos := yypos :: !linePos;
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos));
<S>[^"\\\n]*	=> (addString(charlist,yytext); continue());
<S>\\\n	       	=> (inc lineNum; linePos := yypos :: !linePos;
		    YYBEGIN F; continue());
<S>\\[\ \t]   	=> (YYBEGIN F; continue());
<F>\n		=> (inc lineNum; linePos := yypos :: !linePos; continue());
<F>{ws}		=> (continue());
<F>\\		=> (YYBEGIN S; stringstart := yypos; continue());
<F>.		=> ((#1(argument)) (!stringstart,yypos) "unclosed string";
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos+1));
<S>\\t		=> (addString(charlist,"\t"); continue());
<S>\\n		=> (addString(charlist,"\n"); continue());
<S>\\\\		=> (addString(charlist,"\\"); continue());
<S>\\\"		=> (addString(charlist,"\""); continue());
<S>\\\^[@-_]	=> (addString(charlist,str (chr(ordof(yytext,2)-ord(#"@")))); continue());
<S>\\[0-9]{3}	=>
 (let val x = ordof(yytext,1)*100
	     +ordof(yytext,2)*10
	     +ordof(yytext,3)
	     -(ord(#"0")*111)
  in (if x>255
      then (#1(argument)) (yypos,yypos+4) "illegal ascii escape"
      else addString(charlist,str (chr x));
      continue())
  end);
<S>\\		=> ((#1(argument)) (yypos,yypos+1) "illegal string escape";
		    continue());


