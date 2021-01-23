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
(* For generating a heap image (and script) under SML/NJ *)

signature JERSEYMAIN = sig

  val export : string (* e.g. "stardust-nj" *) -> unit

end


structure Jerseymain : JERSEYMAIN = struct

  fun writeHeapScript name =
      let val suffix = SMLofNJ.SysInfo.getHeapSuffix()
          val heapName = name ^ "." ^ suffix
          val scriptName = name
          val stream = TextIO.openOut scriptName
          val scriptContents =
                   "#!/bin/sh\n"
                 ^ "\n"
                 ^ "/usr/local/smlnj/bin/sml @SMLload=" ^ heapName ^ " $*"
                 ^ "\n"
          val _ = TextIO.output (stream, scriptContents)
          val _ = TextIO.closeOut stream
          val _ = OS.Process.system ("chmod u+x " ^ scriptName)
      in
          ()
      end

  (* Export executable *)

  fun export name =
    let val _ = writeHeapScript name
    in
        SMLofNJ.exportFn (name,
                        fn (_,args) => Stardust.do_args args)
    end

end (* structure Jerseymain *)
