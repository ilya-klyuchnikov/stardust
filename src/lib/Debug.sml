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
(* File: Debug.sml
  Author: Joshua Dunfield
  Contents: Debug-print library with module categories.
 
  Usage:
  API DESCRIPTION OBSOLETE

   - show, showAll, showNone determine which categories will be printed.
 
   - For each category/module, make debug-printer functions:

      val (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [...])

   - `print' takes a thunk; `prnt' (misspelled) takes a string.
     If debugging is turned off, `print' is much more efficient
      whenever computing the string is at all nontrivial.

  TODO: Functorize.  Have one debug-functor for each category; the numbers
    then become debugging levels per category, allowing one to incrementally 
    crank up verbosity for the module of interest.  Have a single module whose `show'
    is propagated to all debug-functors.
*)

signature DEBUG = sig

  type category
  
  val register : {full_name : string,
                  short_name : string}
                 ->
                 {dprint : (unit -> string) -> unit,
                  dprnt : string -> unit
                 (* fail : string -> 'a   Can't, because no first-class polymorphism! *)
                 }
  
  (* In most cases, you should use `makeFunctions' rather than `print'/`prnt' directly *)
(*
  val print : flags -> (unit -> string) -> unit
  val prnt : flags -> string -> unit
  val toFlags : int list -> flags
*)
  exception StdExcept of string * string
  val makeFail : category -> string -> 'a
  
  val fromFull : string -> category option
  val from : string -> category option
  val toString : category -> string
  
  val show : string -> unit
  val hide : string -> unit
  
  val show' : category -> unit
  val hide' : category -> unit
  val showAll : unit -> unit
  val hideAll : unit -> unit
  
(*  
  exception StdExcept of string * string
  val makeFail : string -> string -> 'a
*)
  
  datatype entry =
      Entry of {full_name : string,
                short_name : string,
                show : bool ref}
  val entries : entry option array
  
  val dump : unit -> unit

  (* Same interface as `dprint', but always prints *)
  val pprint : (unit -> string) -> unit  

end (* signature DEBUG *)



structure Debug :> DEBUG = struct
  
  type category = int
  
  datatype entry =
      Entry of {full_name : string,
                short_name : string,
                show : bool ref}
  
  val max_entries = 128
(*  val count = ref 0 *)
  val entries : entry option array = Array.tabulate (max_entries, fn index => NONE)
  
  fun fromFull name =
      case Array.findi (fn (_, NONE) => false | (_, SOME (Entry{full_name, ...})) => name = full_name) entries of
          SOME (index, _) => SOME index
        | NONE => NONE
  
  fun from name =
      case Array.findi (fn (_, NONE) => false | (_, SOME (Entry{full_name, short_name, ...})) => (name = short_name) orelse (name = full_name)) entries of
          SOME (index, _) => SOME index
        | NONE => NONE
  
  fun getName index =
      case Array.sub (entries, index) of
          SOME (Entry{full_name, ...}) => full_name
        | NONE => "--"

  fun toString index =
      case Array.sub (entries, index) of
          SOME (Entry{full_name, short_name, show}) => "Entry{" ^ full_name ^ " (" ^ short_name ^ "): " ^ "show = " ^ Bool.toString (!show) ^ "}"
        | NONE => "--"

  fun dump () =
      Array.appi (fn (index, _) => print (toString index ^ "\n")) entries
  
  fun setShow index value =
      case Array.sub (entries, index) of
          SOME (Entry{show, ...}) => show := value
        | NONE => ()

  fun show' index = setShow index true
  fun hide' index = setShow index false

  fun show name = show' (Option.valOf (from name))
  fun hide name = hide' (Option.valOf (from name))
  
  fun showAll () =
      Array.appi (fn (index, _) => show' index) entries

  fun hideAll () =
      Array.appi (fn (index, _) => hide' index) entries

  fun register {full_name, short_name} =
      case from full_name of
          NONE => 
             let in
                 case Array.findi (fn (index, entry) => not (Option.isSome entry)) entries of
                     NONE => (dump(); print "Debug.register: out of space\n" ; raise Subscript)
                   | SOME (index, _) =>
                         let val showRef = ref false
                             val new = Entry{full_name= full_name, short_name= short_name, show= showRef}
                             fun dprint susp_s =
                                 if !showRef then
                                     TextIO.print (full_name ^ ": " ^ susp_s() ^ "\n")
                                 else
                                     ()
                             fun dprnt s = dprint (fn () => s)
                         in
                             Array.update (entries, index, SOME new);
                             {dprint= dprint,
                              dprnt= dprnt}
                         end
             end
        | SOME index => 
               (Array.update (entries, index, NONE);
                register {full_name = full_name, short_name= short_name})


  exception StdExcept of string * string

  fun printStderr s = TextIO.output (TextIO.stdErr, s)

  fun makeFail index s =
      let val name = getName index
      in
          printStderr ("\nFailure: " ^ name ^ ": " ^ s ^ "\n"); 
          raise StdExcept (name, s)
      end

  fun pprint s = print (s() ^ "\n")
  
end (* structure Debug *)
