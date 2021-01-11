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
(* Code common to Print and PrintTarget *)

signature PRINTLIB = sig

  type ppstream = PrettyPrint.ppstream
  type ppconsumer = PrettyPrint.ppconsumer

  (* given a ppstream operation on 'a and an 'a, produce a string *)
  val p : (ppstream -> 'a -> unit) -> 'a -> string

  val r_width : int ref
  val r_printLocs : bool ref

  val toPPConsumer : TextIO.outstream -> ppconsumer

  val beginBlock : ppstream -> int -> unit
  val endBlock : ppstream -> unit

  val addString  : ppstream -> string -> unit
  val addBreak : ppstream -> int -> unit
  val addNewline : ppstream -> unit
  val addNewlines : ppstream -> int -> unit

  val addLoc : ppstream -> Location.location -> unit

  val sep : string  (* delimiter *)
         -> (ppstream -> 'a -> unit)
         -> ppstream
         -> 'a list
        -> unit
  val sepLine : string (* delimiter *)                           (* Like `sep', but with a newline before the delimiter *)
             -> (ppstream -> 'a -> unit)
             -> ppstream
             -> 'a list
           -> unit
  val addList : {left : string, right : string, separator : string}
             -> (ppstream -> 'a -> unit)
          -> ppstream
          -> 'a list
        -> unit

end (* signature PRINTLIB *)



structure PrintLib :> PRINTLIB = struct

  open Sdml
  structure PP = PrettyPrint

  type ppstream = PP.ppstream
  type ppconsumer = PP.ppconsumer
  
  val r_width = ref 300
  val r_printLocs = ref false

  val beginBlock = PP.begin_block
  val endBlock = PP.end_block
  val addString = PP.add_string
  val addBreak = PP.add_break
  val addNewline = PP.add_newline
  val addNewlines = PP.add_newlines

  fun addLoc pps loc =
     if !r_printLocs then
         (addString pps "<";
          addString pps (Location.toString loc);
          addString pps ">")
     else ()

  fun toPPConsumer stream = 
      {consumer= fn s => TextIO.output (stream, s),
       linewidth= !r_width,
       flush= fn () => TextIO.flushOut stream}

  fun p f x =
     (* 1. Print to a `stream' as a reversed list of strings (to avoid repeated concatenation) *)
     let val saved_width = !r_width
         val result = ref []
         val consumer =
                 {consumer= fn s => (result := s :: !result(*; print ("\n" ^ "+++ " ^ s ^ "\n")*)),
                  linewidth= 100000,
                  flush= fn () => ()}
     in
        r_width := 200;
        
        PrettyPrint.with_pp consumer (fn pps => (f pps x;
                                                 PrettyPrint.flush_ppstream pps));
        r_width := saved_width;

        (* 2. Reverse and concatenate *)
        String.concat (List.rev (!result))
     end



  fun sep delim pp pps list = case list of
       [] => ()
    | [x] => pp pps x
    | x::xs =>
          (pp pps x;
           addBreak pps 0;
           addString pps delim;
           addBreak pps 0;
           sep delim pp pps xs)

  fun sepLine delim pp pps list = case list of
       [] => ()
    | [x] => pp pps x
    | x::xs =>
         (pp pps x;
          addNewline pps;
          addString pps delim;
          sepLine delim pp pps xs)

  fun addList {left, right, separator} pp pps list = 
      (addString pps left;
       sep separator pp pps list;
       addString pps right)


end (* structure PrintLib *)
