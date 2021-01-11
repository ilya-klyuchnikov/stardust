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
 * TODO:
 *
 * [ ] filter out noise from SML/NJ response ("structure Main : sig end" etc.)
 *    (need to `open Main'?)
 * [ ] compile line-at-a-time
 * [ ] think about the `print' part of read-eval-print; it may be too hard to be worth doing properly atm
 *)

signature TOPLEVEL = sig

  val sml_compiler : string ref   (* [path]name of SML/NJ; default "sml" *)

  val run : {do_args_fn : string list -> OS.Process.status} -> OS.Process.status

  val r_transcript : int ref
  
end (* signature TOPLEVEL *)


structure Toplevel :> TOPLEVEL  = struct
  
  structure T = TextIO
  structure ToplevelPiper = PiperFn (struct end)
  structure Piper = ToplevelPiper
  val r_transcript = Piper.r_transcript

  exception Quit

  val _ = Stardustrc.refresh()
  val sml_compiler = ref (Stardustrc.get (fn Stardustrc.Smlnj {path} => path))

  val {dprint, ...} =
          Debug.register {full_name= "Toplevel",
                          short_name= "Top"}

  fun print_with_indent n s =
      let val lines = String.fields (fn ch => ch = #"\n") s
          fun spaces n = if n <= 0 then "" else (spaces (n - 1)) ^ " "
          fun print_lines [] = ()
            | print_lines [""] = ()
            | print_lines (one::rest) =
                 (print (spaces n);
                  print one;
                  print "\n";
                  print_lines rest)
      in
          print_lines lines
      end

  fun run {do_args_fn : string list -> OS.Process.status} =
      let
          val prompt = "stardust> "
          val prompt2 = "stardust>> "

          fun get prompt infile =
              let in
                  T.output (T.stdOut, prompt);
                  T.flushOut (T.stdOut);
                  T.inputLine infile
              end

          val session =
              Piper.launch_session {programPath= !sml_compiler, arguments= []}

          fun mkCookie t =
              let val timeString = Int.toString (Int.fromLarge (IntInf.mod (Time.toSeconds t, 100000)))
                  val quotedPrefix = "\\250" ^ timeString ^ "\\251"
                  val prefix = "\250" ^ timeString ^ "\251"
              in 
                  fn n => (quotedPrefix ^ n ^ "@", prefix ^ n ^ "@")
              end
          val cookie = mkCookie (Time.now ())
          val (quotedCookie1, cookie1) = cookie "1"
          val (quotedCookie2, cookie2) = cookie "2"

          fun matchesCookie cookie args = 
              let val args = String.concat (List.rev args)
                  (* val _ = print ("<<< " ^ args ^ " >>>\n") *)
              in
                  String.isSuffix cookie args
              end

          fun matchesEither cookie1 cookie2 args = 
              let val args = String.concat (List.rev args)
                  (* val _ = print ("<<<< " ^ args ^ " >>>>\n") *)
              in
                  String.isSuffix cookie1 args
                  orelse
                  String.isSuffix cookie2 args
              end              

          val _ =
              (* Prepare SML/NJ: Eat the greeting *)
              Piper.transact_session session {input= "4444;\n",
                                              outputSync= matchesCookie "- "}

          val _ =
              (* Prepare SML/NJ: Make the prompts unique *)
              Piper.transact_session session {input= "(Control.primaryPrompt := \"" ^ quotedCookie1 ^ "\", "
                                                   ^ "Control.secondaryPrompt := \"" ^ quotedCookie2 ^ "\");"
                                                   ^ "\n",
                                              outputSync= matchesCookie cookie1}
          
          fun help () =
              print ("Input syntax:\n"
                   ^ "  ,quit              Quit\n"
                   ^ "  ,compile name      Compile .sdml to .sml\n"
                   ^ "  ,use name          Use .sml target\n"
                   ^ "  ,load name         Compile and use\n"
                   ^ "  ,tunnel text       Pass text directly to SML/NJ\n"
                   ^ "  exp                Evaluate expression (compile + use)\n"
                   ^ "  decs               Bind declarations   (compile + use)\n"
                   )
          
          fun compile args =
              OS.Process.isSuccess (do_args_fn args)

          fun suffix n string =
              String.substring (string, String.size string - n, n)

          fun dropSuffix n string =
              String.substring (string, 0, String.size string - n)

          fun tunnel string =
              let val sml_response =
                      Piper.transact_session session {input= string ^ "\n",
                                                      outputSync= matchesEither cookie1 cookie2}
              in
                  if String.isSuffix cookie2 sml_response then
                      (* read SML/NJ secondary prompt: continuation line *)
                        (* strip prompt *)
                          let val sml_response = dropSuffix (String.size cookie2) sml_response
                              val _ = print sml_response  (* should be empty *)
                              val input = get prompt2 T.stdIn
                          in
                              case input of
                                  NONE => raise Quit   (* quit out of tunnel *)
                                | SOME input =>
                                      tunnel input
                          end
                  else
                      (* read SML/NJ primary prompt: done *)
                        (* strip prompt *)
                          let val sml_response = dropSuffix (String.size cookie1) sml_response
                          in
                              print sml_response;
                              print "\n"
                          end
              end
 
          fun use1 arg = 
              let val {directory, name} = Driver.resolve arg
                  val target_name = name ^ ".stardust.sml"
                  val command_string = "use " ^ "\"" ^ directory ^ target_name ^ "\"" ^ ";" ^ "\n"
                  val _ = dprint (fn () => "use1: target_name = \"" ^ target_name ^ "\"")
                  val _ = dprint (fn () => "use1: command_string = <" ^ command_string ^ ">")
                  val sml_response1 = Piper.transact_session session {input = command_string, outputSync= matchesCookie cookie1}
                  val sml_response1 = dropSuffix (String.size cookie1) sml_response1
                  val sml_response2 = Piper.transact_session session {input = "open Main;\n", outputSync= matchesCookie cookie1}
              in
                  print_with_indent 4 (sml_response1);
                  print "\n"
              end
          
          fun use args =
              List.app use1 args
          
          fun handleCommand input =
              let val t = String.tokens Char.isSpace input
              in
                  case t of
                      ",quit" :: _ => raise Quit
                    | ",exit" :: _ => true
                    | ",help" :: _ => (help(); true)
                    | ",compile" :: args =>
                          let val result = compile args
                          in
                             true
                          end
                    | ",use" :: args =>
                          (use args;
                           true)
                    | ",load" :: args =>
                          let val compile_result = compile args
                          in
                              if compile_result then
                                  (use args; true)
                              else
                                  true
                          end
                    | ",tunnel" :: args => (tunnel (String.concat args); true)
                    | _ => false
              end

          fun loop () =
              let val input = get prompt T.stdIn
              in
                  case input of
                      NONE => raise Quit
                    | SOME input =>
                          if handleCommand input then
                              loop()
                          else
                              (print ("> " ^ input);
                               loop())
              end
              handle
                Quit => ()

  in (* body of Toplevel.run *)
      loop ();
      Piper.kill_session session;
      OS.Process.success
  end

end (* structure Toplevel *)
