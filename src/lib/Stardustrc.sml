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
signature STARDUSTRC = sig

  exception SyntaxError

  datatype program_location =
      Local of {path : string}
    | Remote of {hostname : string, portNumber : int}

  datatype stardust_entry =
      Ics of program_location

    | Yices of program_location
    | Yiceslib of {path : string}

    | Cvc3 of program_location
    | Cvc3lib of {path : string}
    | Cvc4 of program_location

    | Smlnj of {path : string}

  type stardustrc = stardust_entry list

  val refresh : unit -> unit
  
  val loadTryingDefaultPaths : unit -> stardustrc

  val load : string -> stardustrc

  val get_from : (stardust_entry -> 'a) -> stardustrc -> 'a

  val get : (stardust_entry -> 'a) -> 'a
  val toString : unit -> string

  val get_with : (*default*)'a -> (stardust_entry -> 'a) -> 'a

  val r_rc : stardustrc ref

  val r_last_pathname : string option ref   (* Pathname of most recently loaded (presumed current) Stardustrc *)

end (* signature STARDUSTRC *)


structure Stardustrc :> STARDUSTRC = struct
  exception SyntaxError

  datatype program_location =
      Local of {path : string}
    | Remote of {hostname : string, portNumber : int}

  fun locationToString loc = case loc of
      Local {path} => path
    | Remote {hostname, portNumber} => hostname ^ ":" ^ Int.toString portNumber

  datatype stardust_entry =
      Ics of program_location
    | Yices of program_location
    | Yiceslib of {path : string}
    | Cvc3 of program_location
    | Cvc3lib of {path : string}
    | Cvc4 of program_location
    | Smlnj of {path : string}

  fun entryToString entry = case entry of
       Ics location => "Ics " ^ locationToString location
     | Yices location => "yices=" ^ locationToString location ^ "  # Yices interface (BROKEN)"
     | Yiceslib {path} => "yiceslib=" ^ path ^ "  # directly linked Yices interface (BROKEN)"
     | Cvc3 location => "cvc3=" ^ locationToString location ^ "  # location of CVC3 binary (interface BROKEN)"
     | Cvc3lib {path} => "cvc3lib=" ^ path ^ "  # directly linked CVC3 interface (BROKEN)"
     | Cvc4 location => "cvc4=" ^ locationToString location ^ "  # location of CVC4 binary"
     | Smlnj {path} => "sml=" ^ path ^ "  # location of SML/NJ"

  type stardustrc = stardust_entry list
  
  fun toString' [] = "\n"
    | toString' (entry::rest) =
         entryToString entry ^ "\n" ^ toString' rest



  fun Silly_TextIO_inputLine ic =
       case TextIO.inputLine ic of
	   NONE => ""
	 | SOME stuff => stuff

  fun readLines file =
      case Silly_TextIO_inputLine file of
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


  
  (* Substitute $HOME for ~ *)
  fun processPath path =
      let val home = case OS.Process.getEnv "HOME" of SOME string => string | NONE => "~"
      in
        Substring.translate (fn #"~" => home
                              | ch => Char.toString ch)
                            (Substring.full path)
      end

  fun strip_from s line =
      let val (prefix, comment) = Substring.position s (Substring.full line)
      in
          Substring.string prefix
      end

  fun parse line =
      (let val line = strip_from "\n" line
           val line = strip_from "#" line
           val key :: rest = String.fields (fn ch => ch = #"=") line
           fun S_separator c sl = 
               List.foldr (fn (x,y) => if (y = "") then x else x^c^y) "" sl
           val rest = S_separator "=" rest  (* Reconstruct in case RHS contains any #"="s *)
       in
           case key of
               "ics" => 
                   Ics (case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *) Local {path= processPath single}
                     | [hostname, portNumberString] =>  (* Remote   hostname:portnumber  *)
                           Remote {hostname= hostname,
                                               portNumber= valOf (Int.fromString portNumberString)})

             | "yices" =>
                   Yices let in case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *) Local {path= processPath single}
(*                     | [hostname, portNumberString] =>  (* Remote   hostname:portnumber  *)
                           Remote {hostname= hostname,
                                               portNumber= valOf (Int.fromString portNumberString)}
*)
                    end

             | "cvc3" =>
                   Cvc3 (case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *)
                           Local {path= processPath single}
                     | [hostname, portNumberString] =>  (* Remote   hostname:portnumber  *)
                           Remote {hostname= hostname,
                                   portNumber= valOf (Int.fromString portNumberString)})
             
             | "cvc3lib" => let in
                   case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *)
                           Cvc3lib {path= processPath single}
                   end

             | "cvc4" =>
                   Cvc4 (case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *)
                           Local {path= processPath single}
                     | [hostname, portNumberString] =>  (* Remote   hostname:portnumber  *)
                           Remote {hostname= hostname,
                                   portNumber= valOf (Int.fromString portNumberString)})

             | "sml" => let in
                   case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *)
                           Smlnj {path= processPath single}
                   end
             
             | "yiceslib" => let in
                   case String.fields (fn ch => ch = #":") rest of
                       [single] => (* Local path *)
                           Yiceslib {path= processPath single}
                   end
      end)
      handle _ =>   (* Match, Option, ...  possible *)
           raise SyntaxError

  val r_rc : stardustrc ref = ref []
  val r_last_pathname : string option ref = ref NONE

  fun raw_load path =
      let val lines = readFile path
          val _ = r_last_pathname := SOME path
      in
          List.map parse (List.filter (fn line => not (List.all Char.isSpace (explode line) orelse (String.isPrefix "#" line))) lines)
      end

  fun is_executable pathname =
     let val result = OS.Process.system("test -x " ^ pathname)
     in
         OS.Process.isSuccess result
     end

  fun find_in_PATH program_name =
      let val path_var = Option.valOf (OS.Process.getEnv "PATH")
          val paths = String.fields (fn ch => ch = #":") path_var
      in
          case List.find (fn path => is_executable (path ^ "/" ^ program_name)) paths of
              NONE => NONE
            | SOME path => SOME (path ^ "/" ^ program_name)
      end

  fun supplement_with list {exists, key, pathf} =
      case List.find exists list of
          SOME _ => list
        | NONE => 
              let in case find_in_PATH key of
                         NONE => list
                       | SOME path => (pathf path) :: list
              end
    
  fun supplement list =
      let val list = supplement_with list {exists= fn Cvc4 _ => true | _ => false,
                                      key= "cvc4",
                                      pathf= fn path => Cvc4 (Local {path= path})
                                     }
          val list = supplement_with list {exists= fn Smlnj _ => true | _ => false,
                                           key= "sml",
                                           pathf= fn path => Smlnj {path= path}
                                          }
      in
          list
      end


  fun load path =
      let val list = raw_load path
      in
          supplement list
      end

  fun loadTryingDefaultPaths () =
      let val home = Option.valOf (OS.Process.getEnv "HOME")
          val default = home ^ "/" ^ ".stardustrc"
      in
          let in
              load default
          end
          handle
             IO.Io _ =>   (* File not found *)
                  let in
                     (* print "$HOME/.stardustrc not found\n";
                      OS.Process.exit OS.Process.failure *)
                     (* Return empty list, plus defaults *)
                     supplement []
                  end
           | SyntaxError => 
                  let in
                      print "syntax error in $HOME/.stardustrc\n";
                      OS.Process.exit OS.Process.failure
                  end
      end

  fun refresh () =
      r_rc := loadTryingDefaultPaths()

  fun get_from f rc =
      case rc of
          [] => raise Empty
        | entry :: rest =>
              let in (f (entry)) handle Match => get_from f rest
              end
  
  fun get f = get_from f (!r_rc)  

  fun toString () = toString' (!r_rc)
  
  fun get_with default f =
       let in
           get_from f (!r_rc)  
       end
       handle Empty => default
      
end (* structure Stardustrc *)
