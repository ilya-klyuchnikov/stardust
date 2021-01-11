(* Derived from a copyrighted work in the SML/NJ user guide (?) *)

signature TIMING = sig

    val timeit : ('a -> 'b) -> 'a -> string * 'b
    
end


structure Timing : TIMING = struct

  (*
   * Timer from SML/NJ user guide
   *)
  fun timeit f x =
      let open Timer
          open Time
          val t = startCPUTimer ()
          val startTime = Time.now ()
          val z = f x
          val endTime = Time.now ()
          val {gc, sys, usr} = Silly.Timer_checkCPUTimer t
      in
          ((Time.toString (usr + gc + sys) ^ " / wall " ^ Time.toString (endTime - startTime)), z)
      end

end
