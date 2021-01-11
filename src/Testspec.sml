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
signature TESTSPEC = sig

  exception SyntaxError

  datatype testcase =
      Testcase of {path : string, shouldSucceed : bool}

  type testspec

  val load : string -> testspec
  val map : (testcase -> 'a) -> testspec -> 'a list
  val app : (testcase -> unit) -> testspec -> unit
  val toString : testspec -> string
end



structure Testspec :> TESTSPEC = struct
  
  exception SyntaxError

  datatype testcase =
      Testcase of {path : string, shouldSucceed : bool}

  type testspec = testcase list
  
  fun readLines file =
      case Silly.TextIO_inputLine file of
          "" => []
        | line => line :: (readLines file)
  
  fun readFile path =
      let 
          val file = TextIO.openIn path
          val lines = readLines file
      in 
          TextIO.closeIn file;
          lines
      end

  fun parse line =
      if List.all Char.isSpace (explode line) then
          NONE
      else
        (let val line = List.hd (String.fields (fn ch => ch = #"#") line)
             val line = (implode o List.rev o List.tl o List.rev o explode) line
             val fields = String.fields (fn ch => ch = #"=") line
             val key :: rest = fields
             val rest = Separate.list "=" rest  (* Reconstruct in case RHS contains any #"="s *)
             val rest = implode (List.filter (fn ch => not (Char.isSpace ch)) (explode rest))
         in
             case key of
                 "test" => SOME let in
                     case String.fields (fn ch => ch = #":") rest of
                         [single] => raise SyntaxError
                       | [pathname, shouldSucceedString] =>
                             let val shouldSucceed = case shouldSucceedString of
                                 "+" => true
                               | "-" => false
                               | _ => raise SyntaxError
                             in
                                 Testcase{path= pathname, shouldSucceed= shouldSucceed}
                             end
                     end
        end)
        handle _ =>   (* Match, Option, ...  possible *)
             raise SyntaxError

  fun load path =
      let val lines = readFile path
      in
          List.mapPartial parse (List.filter (fn line => not (String.isPrefix "#" line)) lines)
      end
  
  fun map f spec = List.map f spec

  fun app f spec = List.app f spec

  fun specToString (Testcase{path, shouldSucceed}) =
      "test= " ^ path ^ " : " ^ (case shouldSucceed of true => "+" | false => "-")

  fun toString spec =
      Separate.list "\n" (map specToString spec) ^ "\n"
  
end  (* structure Testspec *)
