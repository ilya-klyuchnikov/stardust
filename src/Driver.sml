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
signature DRIVER = sig

  type input = {name_to_print : string, 
                infile : string,
                outfile : string,
                dfile : string option}
  type result = {source: Sdml.program, 
                 prelude: string,
                 elaboration: Sdml.program} option
  type result_with_timings = {result : result, parse_time : string, compile_time : string}
  
  val parse : string -> string -> Sdml.program
  
  val stardust : input -> result_with_timings

  val r_print_program : bool ref  (* default: false *)
  val r_print_elaboration : bool ref  (* default: true *)
  val r_width : int ref
  val r_library_file : string ref        (* defaults to "lib_basis" (file must be in ../glue/ ) *)
  val r_header_file : string ref        (* defaults to "header.sml" (file must be in ../glue/ ) *)
  val r_footer_file : string ref        (* defaults to "footer.sml" (file must be in ../glue/ ) *)
  val check : {name : string, directory : string} -> result_with_timings
  
  val c : string -> bool       (* c s = check ../examples/s.sdml *)
  val c' : string -> bool      (* like c, but also generate debugging files *)
  
  val test : string    (* name of test spec  -- if "", uses "standard.test" *)
             -> bool  (* true iff all tests passed *)
  
  val sdml_elaborate : {print_injection_stages : bool,
                              print_final_source_program : bool,
                              print_elaboration : bool,
                              debug_file : string option,
                              header_path : string,
                              footer_path : string,
                              name_to_print : string}
                       -> (Sdml.program * (*outpath=*)string)
                     -> {source: Sdml.program,
                         prelude: string,
                         elaboration: Sdml.program} option

  val resolve : string -> {directory : string, name : string} 
                              (* convert e.g. "dyn" -> "../examples/stardust" + "dyn",
                               but if .sdml given, use as is *)

  val process_file : string (*infile*) -> bool
end (* signature DRIVER *)



structure Driver :> DRIVER = 
struct

  val {dprint, ...} =
          Debug.register {full_name= "Driver",
                          short_name= "Driver"}

  type input = {name_to_print : string, 
                infile : string,
                outfile : string,
                dfile : string option}
  type result = {source: Sdml.program, 
                 prelude: string,
                 elaboration: Sdml.program} option
  type result_with_timings = {result : result, parse_time : string, compile_time : string}
  
  local
      val index = Option.valOf (Debug.from "Driver")
  in
      fun fail s =
          Debug.makeFail index s
  end

  val lib_prefix = "../glue"
  val r_library_file = ref ("lib_basis")
  val r_header_file = ref ("header.sml")
  val r_footer_file = ref ("footer.sml")
  
  val r_width = ref 400
  val r_print_program = ref false
  val r_print_elaboration = ref true
  

  fun read_header header_path =
      let val stream = TextIO.openIn header_path
          val vec = (TextIO.inputAll stream) : string
          val _ = TextIO.closeIn stream
      in
          vec
      end

  fun sdml_dump_X (printer, suffix) dfile (s: string) p = 
      case dfile of
        SOME f => 
            (let val stream = TextIO.openOut (f ^ "_" ^ s ^ suffix)
             in
                 printer stream p; 
                 TextIO.closeOut stream 
             end;
             p)
      | NONE => p

  val sdml_dump = sdml_dump_X (Print.print, ".sdml")

  fun sdml_elaborate  {print_injection_stages : bool,
                  print_final_source_program : bool,
                  print_elaboration : bool,
                  debug_file= dfile,
                  header_path : string,
                  footer_path : string,
                  name_to_print : string}
                  (the_sdml, outpath)
 =
    let val _ = Stardustrc.refresh ()
        val _ = sdml_dump dfile "=raw" the_sdml
        val _ = if print_injection_stages then
                    (Print.print TextIO.stdOut the_sdml; print "\n--------------------\n\n")
                else ()
    in
      case Sortcheck.check the_sdml of
          (true, the_sdml) =>
              let fun printProgram string the_sdml =
                  if print_injection_stages then
                      (Print.print TextIO.stdOut the_sdml; print string)
                  else
                      ()

                  val the_sdml = Inject.inject_types the_sdml
                  val _ = printProgram "\n\nABOVE: after injecting; BELOW: after flattening\n" the_sdml
                  val the_sdml = Inject.flatten_productsort_quantifiers the_sdml
                  val _ = printProgram "\n\nABOVE: after flattening; BELOW: after eliminating subset sorts\n" the_sdml
                  val the_sdml = Inject.eliminate_subset_sorts the_sdml

                  val _ = printProgram "\n\n" the_sdml
                  val _ = sdml_dump dfile "=inj" the_sdml

                  val lnf = Letnormal.translate_program the_sdml
                  val _ = sdml_dump dfile "=let" lnf
                  val _ =
                      if print_final_source_program then
                          (Print.print TextIO.stdOut lnf; print "\n\n")
                      else ()

                  val (t0, result) =
                          Timing.timeit Typecheck.typecheck lnf

                  fun print_output_program outstream (header, footer) {source, elaboration, prelude} =
                      let fun print s = TextIO.output (outstream, s)
                      in
                          print "\n(* === Elaborated header: === *)\n\n";
                          print header;
                          print "\n(* === Elaborated prelude: === *)\n\n";
                          print prelude;
                          print "\n\n(* === Elaborated program body: === *)\n";
                          PrintTarget.printTarget outstream elaboration;
                          print "\n\n(* === Footer: === *)\n";
                          print footer
                      end

                  val _ =
                      case result of
                          NONE => ()
                        | SOME record =>
                              let val header = read_header header_path
                                  val footer = read_header footer_path
                              in
                                  if print_elaboration then
                                     print_output_program TextIO.stdOut (header, footer) record
                                  else ();
                                  let val outstream = TextIO.openOut outpath
                                  in
                                      print_output_program outstream (header, footer) record;
                                      TextIO.closeOut outstream;
                                      print ("Wrote target program to " ^ outpath ^ "\n")
                                  end
                              end

(*  double-check; currently fails due to insufficient type annotations in elaborated program
                  val result =
                      case result of 
                          NONE => NONE
                        | SOME {elaboration, ...} => Typecheck.typecheck elaboration
*)
              in
                  print ("Typecheck: \""^name_to_print ^ "\": " ^ t0^"\n");
                  result
              end
        | (false, _) => NONE
    end


  fun parse library_file infile =
      (Indexing.reset ();
       ParseLib.reset ();
       Parse.parse [lib_prefix ^ "/" ^ !r_library_file ^ ".sdml", infile ^ ".sdml"]
      )


  fun stardust {name_to_print, infile, outfile, dfile} =
      let 
          val sdml_elaborate = sdml_elaborate {print_injection_stages= !r_print_program,
                                               print_final_source_program= !r_print_program,
                                               print_elaboration= !r_print_elaboration,
                                               debug_file= dfile,
                                               header_path = lib_prefix ^ "/" ^ (!r_header_file),
                                               footer_path = lib_prefix ^ "/" ^ (!r_footer_file),
                                               name_to_print= name_to_print}
          
          val (outname::outdirsplit) = List.rev (Separate.unseparate #"/" outfile)
          val outdir = let val s = Separate.list "/" (List.rev outdirsplit)
                       in
                           if s = "" then "" else s ^ "/"
                       end
          val outdir = if String.isPrefix "/" outfile then
                           "/" ^ outdir    (* Restore initial "/" to absolute path *)
                       else
                           outdir
          val (parse_time, sdml_program) = Timing.timeit (parse (!r_library_file)) infile
          val (compile_time, result) = Timing.timeit sdml_elaborate (sdml_program, outdir ^ outname ^ ".stardust.sml")
      in
         {result= result, 
          parse_time= parse_time, 
          compile_time= compile_time}
      end

  fun booleanize ({result, ...} : result_with_timings)  =
      case result of
          NONE => false
        | SOME {source, prelude, elaboration} => true

  fun check {name, directory} =
      stardust {name_to_print= name,
                infile= directory ^ name,
                outfile= directory ^ name,
                dfile= NONE}

  val examples_d = "../examples/"
  fun c s =
      ( (* Compiler.Profile.setProfMode true;
       Compiler.Profile.reset ();
       Compiler.Profile.setTimingMode true; *)
       let val result = 
               check {name= s, directory= examples_d}
       in
(*       Compiler.Profile.setTimingMode false;
       Compiler.Profile.report TextIO.stdOut;
       Compiler.Profile.reset (); *)
        booleanize result
       end)

  fun c' s =
      booleanize(
            stardust {name_to_print= s,
                      infile= examples_d ^ s,
                      outfile= examples_d ^ s,
                      dfile= SOME (examples_d ^ s)}
      )

(* end *)


(*  Moved to file "standard.test"
  val tests = [("case1", true),
               ("case1x", false),
               ("case2", true),
               ("c1", true),
               ("c3", true),
               ("ctxanno1", true),
               ("ctxanno1x1", false),
               ("ctxanno1x2", false),
               ("ctxanno1x3", false),
               ("left", true),
               ("littlesect", true),
               ("not", true),
               ("slack", true),
               ("refine", true),
               ("redblue", true),
               ("tups", true),
               ("double", true),
               ("double2", true),
               ("mapfilter", true),
               ("exhaust1", false),
               ("exhaust2", true),
               ("memo3", false)
               ]
*)
  fun tests name = Testspec.load ("../examples/" ^ name)

  fun test specname =
      let val specname = case specname of
                             "" => "standard.test"
                           | specname => specname
          val dead = ref false
          fun set_led flag =
              OS.Process.system (if flag then "xset led" else "xset -led")

          val led_flag = ref false

          fun tfun ((s, shouldSucceed), succeeded) = 
              let val msg =
                      case (shouldSucceed, succeeded) of
                          (true, SOME true) => "OK (+)"
                        | (true, SOME false) => (dead := true; "FAILED, should succeed")
                        | (true, NONE) => (dead := true; "BOMBED, should succeed")
                        | (false, SOME true) => (dead := false; "SUCCEEDED, should fail (UNSOUND)")
                        | (false, SOME false) => "OK (-)"
                        | (false, NONE) => (dead := true; "BOMBED, should fail")
              in
                  print ("==== test " ^ s ^ ".sdml:          " ^  msg ^ "\n")
              end
          val (tTotal, test_results) = Timing.timeit (fn () => Testspec.map
              (fn Testspec.Testcase{path= s, shouldSucceed= shouldSucceed} =>
               let val _ = (led_flag := not (!led_flag); set_led (!led_flag))
               in
                   ((s, shouldSucceed), (SOME (c s) handle exn =>
                                         (case exn of
                                              Solve.SolverStartupFailed => print "*** Solver startup failed\n"
                                            | exn => raise exn; NONE)))
               end)
              (tests specname)) ()
      in
          app tfun test_results;
          if !dead then
              (set_led true;
               print "\n*** FAILED TESTS ***\n\n")
          else
              (set_led false;
               ());
          print ("Total time: " ^ tTotal ^ "\n");
          not (!dead)
      end



  fun resolve infile =
      (* If the argument ends with ".sdml", interpret it as a complete (relative) pathname.
         If it doesn't end with ".sdml", interpret it as the name of an example in
         the ../examples directory. *)

      if String.isSuffix ".sdml" infile then

           let
               (* Remove the suffix, which `check' can't handle. *)
               val infile = String.substring (infile, 0, String.size infile - String.size ".sdml")

               (* Split into directory and name *)
               val inname::indirsplit = List.rev (Separate.unseparate #"/" infile)
               val indir = let val s = Separate.list "/" (List.rev indirsplit)
                           in
                               if s = "" then "" else s ^ "/"
                           end
                    (* Separate.unseparate just drops empty components, so
              absolute paths like "/Users/joshua/x.sdml" become "Users/joshua/x.sdml".
             Patch that up: *)
               val indir = if String.isPrefix "/" infile then
                                     "/" ^ indir
                           else
                               indir
           in
               {name= inname, directory= indir}
           end

        else

           let
               (* Split into directory and name *)
               val inname::indirsplit = List.rev (Separate.unseparate #"/" infile)
           in
               case indirsplit of
                   [] =>    (* just a path given *)
                           {name= inname, directory= examples_d}
                 | _ => 
                       let val indir = let val s = Separate.list "/" (List.rev indirsplit)
                               in
                                   if s = "" then "" else s ^ "/"
                               end
                             (* Separate.unseparate just drops empty components, so
                         absolute paths like "/Users/joshua/x.sdml" become "Users/joshua/x.sdml".
                         Patch that up: *)
                           val indir = if String.isPrefix "/" infile then
                                           "/" ^ indir
                                       else
                                           indir
                       in
                           {name= inname, directory= indir}
                       end
           end


  fun process_file infile =
      booleanize (check (resolve infile))

end (* structure Driver *)
