(* Copyright 1996 by AT&T Bell Laboratories *)
(* See SMLNJ-LICENSE file *)
(* precedence.sml *)

signature PRECEDENCE =
sig
  val parse: (''b -> string) -> {apply: 'a * 'a -> 'a, pair: 'a * 'a -> 'a}
                -> ('a, ''b) Sdml.fixitem list * (''b -> Fixity.fixity)
                -> 'a
end (* signature PRECEDENCE *)


structure Precedence :> PRECEDENCE = 
struct    

    local 
        structure F = Fixity
    in 
        val {dprint, ...} =
           Debug.register {full_name= "precedence",
                           short_name= "precedence"}

        local
            val index = Option.valOf (Debug.from "precedence")
        in
            fun fail s =
                Debug.makeFail index s
        end

        datatype ('a, ''b) precStack 
          = INf of ''b * int * 'a * ('a, ''b) precStack
          | NONf of 'a * ('a, ''b) precStack
          | NILf

         fun parse printer {apply,pair} =
           let fun ensureNONf((e,F.NONfix,_),p) = NONf(e,p)
                 | ensureNONf((e,F.INfix _,SOME sym),p) = 
                    (fail
                       ("expression or pattern begins with infix identifier \"" 
                         ^ printer sym ^ "\"");
                         NONf(e,p))
                  | ensureNONf _ = fail "precedence:ensureNONf"

                fun start token = ensureNONf(token,NILf)

                (* parse an expression *)
                fun parse(NONf(e,r), (e',F.NONfix,_)) = NONf(apply(e,e'),r)
                  | parse(p as INf _, token) = ensureNONf(token,p)
                  | parse(p as NONf(e1,INf(_,bp,e2,NONf(e3,r))), 
                          (e4, f as F.INfix(lbp,rbp),SOME sym))=
                      if lbp > bp then INf(sym,rbp,e4,p)
                      else (if lbp = bp
                            then fail "mixed left- and right-associative \
                                                \operators of same precedence"
                            else ();
                            parse(NONf(apply(e2,pair (e3,e1)),r),(e4,f,SOME sym)))

                  | parse(p as NONf _, (e',F.INfix(lbp,rbp),SOME sym)) = 
                      INf(sym,rbp,e',p)
                  | parse _ = fail "Precedence.parse"

                (* clean up the stack *)
                fun finish (NONf(e1,INf(_,_,e2,NONf(e3,r)))) = 
                               finish(NONf(apply(e2,pair (e3,e1)),r))
                  | finish (NONf(e1,NILf)) = e1
                  | finish (INf(sym,_,e1,NONf(e2,p))) = 
                               (fail
                                ("expression or pattern ends with infix identifier \"" 
                                 ^ printer sym ^ "\"");
                                finish(NONf(apply(e2,e1),p)))
                  | finish (NILf) = fail "Corelang.finish NILf"
                  | finish _ = fail "Corelang.finish"

             in fn (items as item1 :: items',env) =>
                  let fun getfix{item,loc,fixity} =
                        (item,  case fixity of NONE => F.NONfix 
                                             | SOME sym => env sym,
                         fixity)

                      fun endloc[{loc,item,fixity}] = fail "precedence:endloc xxx"
                        | endloc(_::a) = endloc a
                        | endloc _ = fail "precedence:endloc"

                      fun loop(state, a::rest) = loop(parse(state,getfix a),rest)
                        | loop(state,nil) = finish(state)

                   in loop(start(getfix item1), items')
                  end
                 | _ => fail "precedence:parse"
            end
    end (* local *)
end (* structure Precedence *)
