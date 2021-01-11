(* Hollowed-out Slind prettyprinter; replaced by simple, straightforward code
  that produces something reasonable.
  Small portions presumably
  
      Copyright 1997(?) Konrad Slind

  Remainder is Copyright 2001-2012 Joshua Dunfield,
  licensed under the terms indicated elsewhere. *)

signature PRETTYPRINT =
sig
  type ppstream
  type ppconsumer = {consumer : string -> unit,
                     linewidth : int,
                     flush : unit -> unit}

  exception PP_FAIL of string

  val mk_ppstream    : ppconsumer -> ppstream

  val add_break      : ppstream -> int -> unit
  val add_newline    : ppstream -> unit
  val add_newlines    : ppstream -> int -> unit
  val add_string     : ppstream -> string -> unit
  val begin_block    : ppstream -> int -> unit
  val end_block      : ppstream -> unit

  val clear_ppstream : ppstream -> unit
  val flush_ppstream : ppstream -> unit

  val with_pp : ppconsumer -> (ppstream -> unit) -> unit
  val pp_to_string : int -> (ppstream -> 'a -> unit) -> 'a -> string

end


structure PrettyPrint : PRETTYPRINT =
struct

open Array infix 9 sub

exception PP_FAIL of string

fun inc r = (r := !r + 1)
fun dec r = (r := !r - 1)

type stack = int list

type ppconsumer = {consumer : string -> unit,
                   linewidth : int,
                   flush : unit -> unit}

datatype state =
   S of {column : int,  (* zero-based *)
         indent : int,
         stack : stack,
         consumer : string -> unit,
         linewidth : int,
         justNewlined : bool,
         flush : unit -> unit}

type ppstream = state ref

fun updateColumns r f =
    case !r of 
        S{column, indent, stack, consumer, linewidth, flush, justNewlined} =>
          r := S{column= f column, indent= indent, stack= stack, consumer= consumer, linewidth= linewidth, flush= flush, justNewlined = justNewlined}

fun jnl r v =
    case !r of 
        S{column, indent, stack, consumer, linewidth, flush, justNewlined} =>
          r := S{column= column, indent= indent, stack= stack, consumer= consumer, linewidth= linewidth, flush= flush, justNewlined = v}

fun updateIndent r f =
    case !r of 
        S{column, indent, stack, consumer, linewidth, flush, justNewlined} =>
          r := S{column= column, indent= f indent, stack= stack, consumer= consumer, linewidth= linewidth, flush= flush, justNewlined = justNewlined}

fun mk_ppstream {consumer, linewidth, flush} =
      ref (S{consumer = consumer,
        linewidth = linewidth,
        stack = [],
        flush = flush,
        column = 0,
        indent = 0,
        justNewlined = true})

 val space = #" "
 fun mk_space (0,s) = String.implode s
   | mk_space (n,s) = mk_space((n-1), (space::s))
 val space_table = Vector.tabulate(100, fn i => mk_space(i,[]))
 fun spaces n = Vector.sub(space_table,n)
                            handle Subscript  =>
                                  if n < 0 then ""
                                  else let val n2 = n div 2
                                           val n2_spaces = spaces n2
                                           val extra = if (n = (2*n2)) then "" else " "
                                       in
                                           String.concat [n2_spaces, n2_spaces, extra]
                                       end

fun cr ofn = ofn ("\n")

val cr = fn ref (S{consumer,...}) => cr consumer

datatype newline_reason = Overflow | User | Block
fun reasonToString r = case r of
     Overflow => "Overflow"
   | User => "User"
   | Block => "Block"

fun newline r (s as ref (S{column, linewidth, indent, ...})) =
      ( (*
         print ("\n:::::newline (" ^ reasonToString r ^ ") " ^ "column = " ^ Int.toString column ^ "; linewidth = " ^ Int.toString linewidth
              ^ "; indent = " ^ Int.toString indent);
         *)
       cr s;
       updateColumns s (fn _ => 0))

fun add_newline'' r (s as ref(S{justNewlined, ...})) =
    if justNewlined then
        ()
    else
        (newline r s;
         jnl s true)

fun add_newline (s as ref(S{justNewlined, ...})) =
    add_newline'' User s

fun add_newlines' (s as ref(S{justNewlined, ...})) n =
    if n <= 0 then
        ()
    else
        (newline User s;
         add_newlines' s (n - 1))

fun add_newlines (s as ref(S{justNewlined, ...})) n =
        let val n =
                if justNewlined then n - 1 else n
        in
            add_newlines' s n;
            jnl s true
        end

fun add_string (s as ref (S{column, linewidth, indent, consumer, ...})) string =
    let val n = String.size string
    in
        jnl s false;

            (if column + n >= linewidth then
                 newline Overflow s
             else
                 ());

        let val string = if column < indent then
                             (spaces (indent - column)) ^ string
                         else string
        in            
            consumer string;
            updateColumns s (fn col => col + String.size string)
        end
    end


fun add_break (s as ref (S{column, linewidth, indent, ...})) n =
    add_string s (spaces n)

fun add_indent (s as ref (S{indent, stack, column, consumer, linewidth, flush, justNewlined})) n =
    s := S{indent= indent + n,
           stack= n :: stack,
           column= column,
           consumer= consumer,
           linewidth= linewidth,
           flush= flush,
           justNewlined= justNewlined}

fun begin_block (s as ref (S{column, linewidth, indent, ...})) n =
  (add_indent s n;
   add_newline'' Block s)

fun end_block (s as ref (S{indent, stack= n :: tail, column, consumer, linewidth, flush, justNewlined})) =
   (s := S{indent= indent - n,
           stack= tail,
           column= column,
           consumer= consumer,
           linewidth= linewidth,
           flush= flush,
           justNewlined= justNewlined};
    add_newline'' Block s)


fun clear_ppstream _ = ()
fun flush_ppstream _ = ()


(*---------------------------------------------------------------------------
 * Builds a ppstream, sends pretty printing commands called in f to 
 * the ppstream, then flushes ppstream.
 *---------------------------------------------------------------------------*)
fun with_pp ppconsumer ppfn = 
   let val ppstrm = mk_ppstream ppconsumer
    in ppfn ppstrm;
       flush_ppstream ppstrm
   end
   handle PP_FAIL msg => 
     (print (">>>> PP_FAIL: " ^ msg ^ "\n"))


fun pp_to_string linewidth ppfn ob = 
    let val l = ref ([]:string list)
        fun attach s = l := (s :: !l)
     in with_pp {consumer = attach, linewidth=linewidth, flush = fn()=>()}
                (fn ppstrm =>  ppfn ppstrm ob);
        String.concat (List.rev(!l))
    end


end (* PrettyPrint *)
