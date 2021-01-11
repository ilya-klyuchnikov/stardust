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
structure Parse :> sig
      val parse_one : (ParseLib.env * Sdml.decs) * string -> ParseLib.env * Sdml.program
      val parse : string list -> Sdml.program
   end
=
struct

  open Sdml
  
  val lineNum = ref 1
  val linePos = ref [0]
  
  val anyErrors = ref false

  fun getPos offset (lineNum, linePositions) =
     case linePositions of
        [] => (0, 0)
      | linePos :: rest =>
           if linePos < offset then
              (lineNum, offset - linePos)
           else
              getPos offset (lineNum - 1, rest)

  
  fun toLocation p1 p2 = 
      let val (p1line, p1pos) = getPos p1 (!lineNum, !linePos)
          val (p2line, p2pos) = 
                  if p1 > p2 then (p1line, p1pos)
                  else getPos (p2 - 1) (!lineNum, !linePos)
      in
          Location.fromPositions (p1line, p1pos, p2line, p2pos)
      end

  fun locify p1 p2 exp =
    (toLocation p1 p2, exp)
  
  fun err (p1, p2) s = 
      let
          val (p1line, p1pos) = getPos p1 (!lineNum, !linePos)
      in
          print
               (Int.toString p1line ^ "." ^ Int.toString p1pos
             ^ (if p1 > p2 then ""
                else
                    let val (p2line, p2pos) = getPos (p2 - 1) (!lineNum, !linePos)
                    in
                        "-" ^ Int.toString p2line ^ "." ^ Int.toString p2pos
                    end)
             ^ " Error: " ^  s ^ "\n");
          anyErrors := true
      end
  
  val argument = (err : int * int -> string -> unit,
                  toLocation : int -> int -> Location.location,
                  locify : int -> int -> Sdml.exp -> Sdml.locexp)
  
  val lexarg = {comLevel = ref 0,
                lineNum = lineNum,
                linePos = linePos,
                charlist = ref ([] : string list),
                stringstart = ref 0,
                stringtype = ref true,
                argument = argument}
  
  fun parse_error (s, i, j) = err (i, j) s
  
  structure LrVals = SdmlLrValsFun (structure Token = LrParser.Token);
  structure Lex    = SdmlLexFn (structure Tokens = LrVals.Tokens);
  structure Parser = JoinWithArg (structure ParserData = LrVals.ParserData
                                  structure Lex = Lex
                                  structure LrParser = LrParser);

  fun elaborate (env, typedecsl) startsym_result = 
    let val (env, p) = startsym_result (env, typedecsl)
    in
        (env, p) : ParseLib.env * Sdml.program
    end

  exception ParseFailed

  fun parse_one ((bestowed_env, bestowed_algsl), file) : ParseLib.env * Sdml.program = 
      let
          val f_in =
              (TextIO.openIn file)
              handle IO.Io {name, function, cause} =>
                                  (print ("Failure: Couldn't read file ``" ^ name ^ "''\n"); raise cause)
                   | exn => raise exn
      in
          lineNum := 1;
          linePos := [0];
          anyErrors := false;
          
          let val lexer = Parser.makeLexer (fn n => TextIO.inputN (f_in, n)) lexarg 
              val (result, _) = Parser.parse(0, lexer, parse_error, argument)
          in
              TextIO.closeIn f_in;
              if !anyErrors then 
                  raise ParseFailed
              else
                  elaborate (bestowed_env, bestowed_algsl) result
                  before
                  (if !anyErrors then raise ParseFailed else ())
          end
      end

  fun parse filelist =
      let fun aux env [actual_program] =
                    let val _ = print ("Parsing program file ``" ^ actual_program ^ "'' \n")
                        val (env, program) = parse_one (env, actual_program)
                    in
                        program
                    end
            
            | aux (env, lib_decs) (libfile :: (rest as (_ :: _))) =
                    let val _ = print ("Parsing library file ``" ^ libfile ^ "'' \n")
                        val (env', Program(_, [], (loc, lib_exp))) = parse_one ((env, lib_decs), libfile)
                        fun extract exp = case exp of 
                           Let (decs, (_, exp)) => extract_decs decs @ extract exp
                         | Tuple [] => []
                         | _ => (print ("WARNING: strange library file\n"); [])
                        
                        and extract_decs decs = List.concat (List.map extract_dec decs)
                        
                        and extract_dec (loc1, d as Dec (_, kw, (loc2, exp))) = (extract exp) @ [(loc, d)]
                          | extract_dec (loc, d) = [(loc, d)]
                    in
                        aux (env', lib_decs @ extract lib_exp) rest
                    end
      in
          aux (ParseLib.get_empty_env(), []) filelist
      end

end (* structure Parse *)
