(* Substantially based on SML/NJ 0.93 token.sml.
  See the copyright notice in SMLNJ-LICENSE.
*)

functor SdmlTokenTableFn (Tokens : Sdml_TOKENS) :
    sig
        val checkToken: string * int -> (Tokens.svalue, int) Tokens.token
    end
= 
struct

(* The list of string with their corresponding token.
Note that ML has generous rules about identifier names;
any keyword that might be an identifier goes here, rather
than in the main lex spec. *)

fun process list =
    List.map (fn (string, token) =>
                   let val len = String.size string
                   in
                      (string,
                       fn yypos => token (yypos, yypos + len))
                   end)
             list

val tokenList =
    process
      [("*"      ,  Tokens.ASTERISK),
       ("|"      ,  Tokens.BAR),
       ("="      ,  Tokens.EQUALOP),
       ("#"      ,  Tokens.HASH),

       ("&"      ,  Tokens.AMP),
       ("/"    ,  Tokens.SLASH),
       ("&&"      ,  Tokens.DBLAMP),
       ("//"    ,  Tokens.DBLSLASH),

       ("top"    ,  Tokens.TOP),
       ("bot"    ,  Tokens.BOT),
       ("->"     ,  Tokens.ARROW),
       ("and"    ,  Tokens.AND),
       ("andalso",  Tokens.ANDALSO),
       ("as",  Tokens.AS),
       ("case"   ,  Tokens.CASE),
       ("datatype"  , Tokens.DATATYPE),
       ("datacon",  Tokens.DATACON),
       ("datasort"  , Tokens.DATASORT),
       ("do"  ,  Tokens.DO),
       ("else"   ,  Tokens.ELSE),
       ("end"    ,  Tokens.END),
       ("=>"     ,  Tokens.DARROW),
       ("fn"     ,  Tokens.FN),
       ("fun"    ,  Tokens.FUN),
       ("handle" ,  Tokens.HANDLE),
       ("hint" ,  Tokens.LETHINT),
       ("if"     ,  Tokens.IF),
       ("in"     ,  Tokens.IN),
       ("let"    ,  Tokens.LET),
       ("of"     ,  Tokens.OF),
       ("op"     ,  Tokens.OP),
       ("orelse" ,  Tokens.ORELSE),
       ("primitive"  ,  Tokens.PRIMITIVE),
       ("indexsort"  ,  Tokens.INDEXSORT),
       ("indexfun"  ,  Tokens.INDEXFUN),
       ("indexconstant"  ,  Tokens.INDEXCONSTANT),
       ("indexpred"  ,  Tokens.INDEXPRED),
       ("not"  ,  Tokens.NOT),
       ("raise"  ,  Tokens.RAISE),
       ("rec"    ,  Tokens.REC),
       ("some"    ,  Tokens.SOME),
       ("test'subtype"   ,  Tokens.TESTSUBTYPE),
       ("then"   ,  Tokens.THEN),
       ("try"   ,  Tokens.TRY),
       ("type"   ,  Tokens.TYPE),
       ("unit"   ,  Tokens.UNIT),
       ("val"    ,  Tokens.VAL),
       ("{"      ,  Tokens.LBRACE),
       ("}"      ,  Tokens.RBRACE),
       ("where"  ,  Tokens.WHERE),
       ("with"   ,  Tokens.WITH),
       ("withtype"  , Tokens.WITHTYPE)
     ]


(* Look-up function. If the symbol is found, the corresponding token is
   generated with the position of its begining. Otherwise it is a regular
   identifier. *)
   
fun checkToken (str, yypos) =
  let fun f list = case list of
        [] => Tokens.ID (str, yypos, yypos + size str)
      | (k, v) :: t =>
             if str = k then
                 v yypos
             else
                 f t
  in 
      f tokenList
  end

end (* functor SdmlTokenTableFn *)
