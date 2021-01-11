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
signature STARDUST = sig

  val print_version : unit -> unit   (* Print version & configuration to stderr *)
  
  val do_args : string list -> OS.Process.status    (* called from Mltonmain.sml, Jerseymain.sml *)

  val top : unit -> OS.Process.status

end (* signature STARDUST *)



structure Stardust :> STARDUST = struct

  open Driver
    
  val version = "0.5"
  
  val creation_time = Date.toString (Date.fromTimeLocal (Time.now()))
  val creation_host = Assoc.get (Posix.ProcEnv.uname()) "nodename"
  
  fun printStderr s = TextIO.output (TextIO.stdErr, s)
  
  fun print_version () =
    let in
      printStderr ("Stardust version " ^ version ^ "\n"
           ^ "built " ^ creation_time ^ " on " ^ creation_host ^ "\n"
           ^ "library file name is \"" ^ !r_library_file ^ "\"\n"
           ^ "header file name is \"" ^ !r_header_file ^ "\"\n"
           ^ "footer file name is \"" ^ !r_footer_file ^ "\"\n"
           );

      Stardustrc.refresh();
      printStderr (".stardustrc is " ^ (case !Stardustrc.r_last_pathname of
                                   NONE => "??" 
                                 | SOME s => "\"" ^ s  ^ "\"")
           ^ "\n");
      printStderr ("stardustrc configuration:\n" ^ Stardustrc.toString ())
    end


  fun print_usage_message () =
       (printStderr (
               "Usage: \n"
             ^ "stardust [options] [foo | ../examples/foo.sdml | -T testname]\n"
             ^ "                    ^^^\n"
             ^ "                    no .sdml suffix = use ../examples/foo.sdml\n"
             ^ "\n"
             ^ "   -d | --debug                  Debug.showAll()  (default: Debug.hideAll())\n"
             ^ "  (-w | --width) nnn             Set output width to nnn\n"
             ^ "  (-T | --Test) testname.test    Run test suite specified in testname.test\n"
            );
        OS.Process.failure)      

  fun do_args args =
    let in
        case args of
           "--no-debug"::rest =>
                (Debug.hideAll(); do_args rest)
          | "-d"::rest =>
                (Debug.showAll(); do_args rest)
          | "--debug"::rest =>
                (Debug.showAll(); do_args rest)
  (*
          | "-noMemo" :: rest =>
                (Context.r_memoize := Context.NoMemo; do_args rest)
  *)
          | "-w"::width::rest =>
                (r_width := valOf(Int.fromString width); do_args rest)
          | "--width"::width::rest =>
                (r_width := valOf(Int.fromString width); do_args rest)
          | "-T"::testname::rest =>
                (test testname; OS.Process.success)
          | "--Test"::testname::rest =>
                (test testname; OS.Process.success)
          | "--version"::rest =>
                (print_version(); OS.Process.success)
  (*      | "-t"::library_file::rest => 
                (r_library_file := library_file; do_args rest)
  *)
          | something::rest =>
                let in case explode something of
                     #"-"::_ => (printStderr ("unknown option: " ^ something ^ "\n");
                                 print_usage_message())
                   | _ =>
                         let in case something::rest of
                              infile::nil =>
                                   let in 
                                        (Driver.process_file infile;
                                         OS.Process.success) 
                                        handle e => OS.Process.failure
                                   end

                         end
                end

          | [] => top ()

(*          | _ => 
               print_usage_message()
*)
    end

  and top () =
      Toplevel.run {do_args_fn = do_args}      

end (* structure Stardust *)
