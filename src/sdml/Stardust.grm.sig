signature Sdml_TOKENS =
sig
type ('a,'b) token
type svalue
val DASHEXISTS:  'a * 'a -> (svalue,'a) token
val DASHALL:  'a * 'a -> (svalue,'a) token
val DBLSLASH:  'a * 'a -> (svalue,'a) token
val DBLAMP:  'a * 'a -> (svalue,'a) token
val SLASH:  'a * 'a -> (svalue,'a) token
val AMP:  'a * 'a -> (svalue,'a) token
val BOT:  'a * 'a -> (svalue,'a) token
val TOP:  'a * 'a -> (svalue,'a) token
val LEFTANNO:  'a * 'a -> (svalue,'a) token
val PERIOD:  'a * 'a -> (svalue,'a) token
val SOME:  'a * 'a -> (svalue,'a) token
val WILD:  'a * 'a -> (svalue,'a) token
val TURNSTILE:  'a * 'a -> (svalue,'a) token
val SEMICOLON:  'a * 'a -> (svalue,'a) token
val PLUS:  'a * 'a -> (svalue,'a) token
val MINUS:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val RBRACK:  'a * 'a -> (svalue,'a) token
val LBRACK:  'a * 'a -> (svalue,'a) token
val RBRACE:  'a * 'a -> (svalue,'a) token
val LBRACE:  'a * 'a -> (svalue,'a) token
val HASH:  'a * 'a -> (svalue,'a) token
val EQUALOP:  'a * 'a -> (svalue,'a) token
val DQUESTION:  'a * 'a -> (svalue,'a) token
val DBLCOMMA:  'a * 'a -> (svalue,'a) token
val DBLCOLON:  'a * 'a -> (svalue,'a) token
val DARROW:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val BAR:  'a * 'a -> (svalue,'a) token
val ASTERISK:  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val APOSTROPHE:  'a * 'a -> (svalue,'a) token
val ANTICOLON:  'a * 'a -> (svalue,'a) token
val WITHTYPE:  'a * 'a -> (svalue,'a) token
val WITH:  'a * 'a -> (svalue,'a) token
val WHERE:  'a * 'a -> (svalue,'a) token
val VAL:  'a * 'a -> (svalue,'a) token
val UNIT:  'a * 'a -> (svalue,'a) token
val TYPE:  'a * 'a -> (svalue,'a) token
val TRY:  'a * 'a -> (svalue,'a) token
val THEN:  'a * 'a -> (svalue,'a) token
val TESTSUBTYPE:  'a * 'a -> (svalue,'a) token
val REC:  'a * 'a -> (svalue,'a) token
val RAISE:  'a * 'a -> (svalue,'a) token
val PRIMITIVE:  'a * 'a -> (svalue,'a) token
val ORELSE:  'a * 'a -> (svalue,'a) token
val OP:  'a * 'a -> (svalue,'a) token
val OF:  'a * 'a -> (svalue,'a) token
val NOT:  'a * 'a -> (svalue,'a) token
val LOCAL:  'a * 'a -> (svalue,'a) token
val LETHINT:  'a * 'a -> (svalue,'a) token
val LET:  'a * 'a -> (svalue,'a) token
val INDEXSORT:  'a * 'a -> (svalue,'a) token
val INDEXPRED:  'a * 'a -> (svalue,'a) token
val INDEXFUN:  'a * 'a -> (svalue,'a) token
val INDEXCONSTANT:  'a * 'a -> (svalue,'a) token
val IN:  'a * 'a -> (svalue,'a) token
val IF:  'a * 'a -> (svalue,'a) token
val HANDLE:  'a * 'a -> (svalue,'a) token
val FUN:  'a * 'a -> (svalue,'a) token
val FN:  'a * 'a -> (svalue,'a) token
val END:  'a * 'a -> (svalue,'a) token
val ELSE:  'a * 'a -> (svalue,'a) token
val DO:  'a * 'a -> (svalue,'a) token
val DATATYPE:  'a * 'a -> (svalue,'a) token
val DATASORT:  'a * 'a -> (svalue,'a) token
val DATACON:  'a * 'a -> (svalue,'a) token
val CASE:  'a * 'a -> (svalue,'a) token
val AS:  'a * 'a -> (svalue,'a) token
val ANDALSO:  'a * 'a -> (svalue,'a) token
val AND:  'a * 'a -> (svalue,'a) token
val CHAR: (string) *  'a * 'a -> (svalue,'a) token
val STRING: (string) *  'a * 'a -> (svalue,'a) token
val REAL: (string) *  'a * 'a -> (svalue,'a) token
val INT: (string) *  'a * 'a -> (svalue,'a) token
val TYVAR: (string) *  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature Sdml_LRVALS=
sig
structure Tokens : Sdml_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
