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
signature PIPER = sig
  
  type session

  val session_list : session list ref

  
  val launch_session : {programPath : string,
                       arguments : string list  (* arguments are argv[1..n]; argv[0] := programPath *)
                       } -> session
  
  val launch_remote_session : { hostname : string,
                               portNumber : int
                               } -> session option
  
  (* Write `input', reading until `outputSync output' is true *)
  (* (Probably should use a stream; keeping it simple for now.) *)
  exception TransactTimeout of string  (* response *)
  val transact_session : session
      -> {input : string,
          outputSync : (string list) -> bool (* Return true iff String.concat (List.rev arg) indicates end of output *) }
      -> string

  val transact_yices_silent_session : session
      -> {input : string}
      -> unit

  val makeSillyOutputSync : (string -> bool) -> (string list -> bool)
  
  val kill_session : session -> unit
  
  val kill_all : unit -> unit
  
  val call : {
              programPath: string
            , inputString: string
          } -> string option

(* deprecated  
  val call_cvc : string -> bool option
  val call_svc1 : string -> bool option
  val call_svc2 : string -> bool option
*)

  val start_local_ics : string -> session option
  val start_remote_ics : {hostname : string, portNumber : int} -> session option

  val call_ics : string list -> string -> bool option

  val start_local_cvcl : string -> session option
  val start_remote_cvcl : {hostname : string, portNumber : int} -> session option

  val start_local_cvc4 : string -> session option
  val start_remote_cvc4 : {hostname : string, portNumber : int} -> session option

  val start_local_yices : string -> session option

(*
  val connectToServer : { hostname : string,
                         portNumber : int,
                         password : string
                               } -> session option
  *)
  val invade_Sweden : string -> unit
  val icsTransmissions : int ref
  val r_transcript : int ref   (* 0 = no transcript; 1 = write sent text to transcript;
                                2 = write sent and received text to transcript *)

  val echo : (unit -> string) -> unit

  structure Stats : sig
    val reset : unit -> unit
    val dump : unit -> unit
  end

end (* signature PIPER *)



functor PiperFn (Freshifier : sig end)  :> PIPER = struct

  val r_transcript = ref 0

  structure Stats = struct

     val r_counts : Time.time list ref = ref []
     
     fun reset () =
         r_counts := []
     
     fun datumToString t = Real.toString (t * 1000.0) ^ " ms"
     
     val dumppath = "/tmp/stardust-piper-dump"
     
     fun dump_data() =
         let
              val dumpfile = TextIO.openOut dumppath
              val _ = List.app (fn t => TextIO.output (dumpfile, datumToString (Time.toReal t) ^ "\n")) (!r_counts)
              val _ = TextIO.closeOut dumpfile
         in
             ()
         end

     fun dump () =
         let val total = List.foldl Time.+ (Time.zeroTime) (!r_counts)
             val length = List.length (!r_counts)
         in
             print ("Stats.dump():\n");
             print ("     # calls: " ^ Int.toString length ^ "\n");
             print ("  total time: " ^ Real.toString (Time.toReal total) ^ "  s\n");
             print ("   mean time: " ^ datumToString (Time.toReal total / Real.fromInt length) ^ "\n");
             print ("\n");
             dump_data();
             print ("Data dumped to " ^ dumppath ^"\n\n")
         end

     fun save time =
         r_counts := time :: (!r_counts)
  end
  
  structure String = Silly.String
  val {dprint, dprnt} =
        Debug.register {full_name= "Piper",
                        short_name= "Piper"}

  datatype session =
      ChildProcess of {pid : Posix.IO.pid,
                       outfdToChild : Posix.IO.file_desc,
                       infdFromChild : Posix.IO.file_desc
                      }
    | RemoteProcess of {socket : Socket.active (*Socket.stream    damn phantom types! *) INetSock.stream_sock
                       }

  exception TransactTimeout of string  (* response *)

  fun writeTranscript minLevel input =

      if !r_transcript >= minLevel then
          let
              val transcript = TextIO.openAppend "/tmp/transcript"
              val _ = TextIO.output (transcript, input())
              val _ = TextIO.closeOut transcript
          in
              ()
          end
      else
          let 
(*
              val transcript = TextIO.openAppend "/tmp/transcript"
              val _ = TextIO.output (transcript, "*")
              val _ = TextIO.closeOut transcript
*)
          in
              ()
          end

  fun echo string =
      writeTranscript 1 string

  val session_list : session list ref = ref []

  fun launch_remote_session { hostname,
                             portNumber} =
      let val client = INetSock.TCP.socket()
          val hostent = NetHostDB.getByName hostname
      in
          case hostent of
              NONE => NONE
            | SOME hostent =>
                  let val hostaddr = NetHostDB.addr hostent
                      val _ = Socket.connect(client, INetSock.toAddr (hostaddr, portNumber ))
                      val _ = INetSock.TCP.setNODELAY(client, true)
                      val session = RemoteProcess {socket= client}
                  in
                      session_list := session :: (!session_list);
                      SOME session
                  end
      end before
      writeTranscript 1 (fn () => "launch_remote_session$\n")

  fun write_file name str =
      let val os = TextIO.openOut name
      in TextIO.output(os, str);
          TextIO.closeOut os
      end

  fun call {programPath, inputString} =
      let val tmpIn = "/tmp/piperinput"
          val tmpOut = "/tmp/piperoutput"
          val _ = write_file tmpIn inputString
          val status = OS.Process.system (programPath ^ " < " ^ tmpIn ^ " > " ^ tmpOut)
      in
          if true orelse (OS.Process.isSuccess status)
          then
             let val instream = TextIO.openIn tmpOut
             in
                 SOME (TextIO.inputAll instream)
                 before
                 TextIO.closeIn instream
             end
         else (print ("Piper.call failed\n");
             NONE)
      end

  fun set_nonblocking fd =
      let val (flags, open_mode) = Posix.IO.getfl fd
          val (to, from) = (Posix.IO.O.toWord, Posix.IO.O.fromWord)
          val flags = from (SysWord.orb (to flags, to Posix.IO.O.nonblock))
      in
          Posix.IO.setfl (fd, flags)
      end

  fun set_blocking fd =
      let val (flags, open_mode) = Posix.IO.getfl fd
          val (to, from) = (Posix.IO.O.toWord, Posix.IO.O.fromWord)
          val flags = from (SysWord.andb (to flags, SysWord.notb(to Posix.IO.O.nonblock)))
      in
          Posix.IO.setfl (fd, flags)
      end

  (* nonblockingWrapper : ('a -> 'b) -> 'a -> 'b option
  
     nonblockingWrapper g x evaluates g(x):

     - if g(x) does not raise an exception, returns SOME (g(x));
     - if g(x) raises OS.SysErr(_, Posix.Error.again) (known as EAGAIN), as it is when a nonblocking
         operation "would block" (e.g. a read operation with no data available),
         returns NONE;
     - if g(x) raises any other exception, propagates the exception.
  *)
  fun nonblockingWrapper g x =
      (SOME (g x)) handle OS.SysErr(message, syserror_option) =>
          (case syserror_option of
               SOME errcode => if errcode = Posix.Error.again then
                   NONE
                               else raise OS.SysErr(message, syserror_option)
             | _ => raise OS.SysErr(message, syserror_option))

  fun readString fd =
      let fun rd acc =
          case nonblockingWrapper Posix.IO.readVec (fd, 1(*024*)) of
              NONE => acc
            | SOME vec => 
                  if Word8Vector.length vec = 0 then
                      acc
                  else let val s = Byte.bytesToString vec
(*                           val _ = print (" " ^ s)    *)
                       in
                           rd (acc ^ s)
                       end
      in
          rd ""
      end

  fun makeSillyOutputSync f ss =
      f (String.concat (List.rev ss))
 
  fun Silly_isSuffix s = makeSillyOutputSync (String.isSuffix s)

  fun spinread fd =
      case readString fd of
          "" => spinread fd
        | s => s

  fun launch_session {programPath, arguments} =
      let val {infd= infdToChild (* Child reading from parent *),
               outfd= outfdToChild (* Parent writing to child *) } = Posix.IO.pipe()    (* Pipe of INPUT TO the child *)
          
          val {infd= infdFromChild (* Parent reading from child *),
               outfd= outfdFromChild (* Child writing to parent *) } = Posix.IO.pipe()  (* Pipe of OUTPUT FROM the child *)

(*
          val {infd= infdErrChild (* Parent reading stderr from child *),
               outfd= outfdErrChild (* Child writing stderr to parent *) } = Posix.IO.pipe()  (* Pipe of STDERR FROM the child *)
*)
      in
         case Posix.Process.fork() of

             NONE =>   (* child process *)

                 let val () = Posix.IO.close outfdToChild
                     val () = Posix.IO.dup2 {old= infdToChild, new= Posix.FileSys.stdin}
                     val ()= Posix.IO.close infdToChild

                     val () = Posix.IO.close infdFromChild
                     val () = Posix.IO.dup2 {old= outfdFromChild, new= Posix.FileSys.stdout}
                     val () = Posix.IO.dup2 {old= outfdFromChild, new= Posix.FileSys.stderr}
                     val () = Posix.IO.close outfdFromChild

(*
                     val () = Posix.IO.close infdErrChild
                     val () = Posix.IO.dup2 {old= outfdErrChild, new= Posix.FileSys.stderr}
                     val () = Posix.IO.close outfdErrChild
*)
                     val () = Posix.Process.exec (programPath, programPath::arguments)
                 in  (* Should never get here! *)
                     Posix.Process.exit (Word8.fromInt 99)
                 end


           | SOME child =>   (* parent process *)

                 let val () = Posix.IO.close infdToChild
                     val () = Posix.IO.close outfdFromChild
(*                     val () = Posix.IO.close outfdErrChild *)
(*                     val _ = set_nonblocking infdFromChild *)
                     val session = ChildProcess{pid= child, infdFromChild= infdFromChild, outfdToChild= outfdToChild}
                 in
                      session_list := session :: (!session_list);
                      session
                 end

      end
  
  val timeout = Time.fromSeconds 5

  val icsTransmissions : int ref = ref 0

  fun transact_yices_silent_session (ChildProcess {pid, outfdToChild, infdFromChild}) {input} =
      let
          val _ = (icsTransmissions := !icsTransmissions + 1)
          val n = Posix.IO.writeVec (outfdToChild, Word8VectorSlice.full (Byte.stringToBytes input))
          val _ = dprint (fn () => "wrote (silent) to child[" ^ input ^ "]")
          val _ = writeTranscript 1 (fn () => input)
      in
        ()
      end
 
  fun transact_session (ChildProcess {pid, outfdToChild, infdFromChild}) {input, outputSync} =
      let
(* val _ = SMLofNJ.Internals.ProfControl.profileOff()
val _ = Compiler.Profile.setTimingMode false *)
 (*val _ = Posix.Process.sleep (Time.fromSeconds 1) *)
          val _ = (icsTransmissions := !icsTransmissions + 1)
          val n = Posix.IO.writeVec (outfdToChild, Word8VectorSlice.full (Byte.stringToBytes input))
          val _ = dprint (fn () => "wrote to child: " ^ input)
          val _ = writeTranscript 1 (fn () => input (* ^ "   % " ^ Int.toString (Word32.toInt (Posix.Process.pidToWord pid)) *))
(*          val _ = set_nonblocking infdFromChild *)

          (* spinread : Time.time -> string -> string
              
           Reads repeatedly from infdFromChild.  If no output for the interval `timeout'
           (see above), raise TransactTimeout.

           Note that a looping child that keeps outputting will not trigger the timeout;
           how should we handle that?  Also: Take `timeout' as an argument?
           *)
          fun spinread cutoffTime acc =
              case readString infdFromChild of
                  "" =>   (* Child didn't output anything *)
                          if Time.> (Time.now(), cutoffTime) then
                              raise TransactTimeout (String.concat (List.rev acc))
                          else
                              spinread cutoffTime acc
           | output => let val acc = output :: acc
                           val _ = print ("acc = " ^ String.concat (List.rev acc) ^ "\n.\n")
                       in
                           if outputSync acc then   (* reached end of output *)
                               (let val acc = String.concat (List.rev acc)
                                in
                                    (*print "OUTPUT"; print acc; print "\n"; *) 
                                        acc
                                end)
                           else   (* not at end; bump timer since we got some output *)
                               spinread (Time.+ (Time.now(), timeout)) acc
                       end

          fun spinread acc =
              let val acc = Byte.bytesToString (Posix.IO.readVec (infdFromChild, 1024))  ::  acc
              in
                  if outputSync acc then 
                      (let val acc = String.concat (List.rev acc)
                       in
                           (*print "OUTPUT"; print acc; print "\n"; *) 
                           acc
                       end)
                  else   (* not at end; bump timer since we got some output *)
                      spinread acc
              end
      in
let (* val _ = print "bef. spinread\n" *)
    val r =
          spinread []
    (* val _ = print "after spinread\n" *)
in
    writeTranscript 2 (fn () => "====  " ^ r ^ "\n");
    r
end
(*
          spinread (Time.+ (Time.now(), timeout)) []
*)
(*        before
          SMLofNJ.Internals.ProfControl.profileOn()
*)
      end
    | transact_session (RemoteProcess {socket}) {input, outputSync} =
        let val n = Socket.sendVec (socket, Word8VectorSlice.full (Byte.stringToBytes input))
            val _ = dprint (fn () => "wrote to socket: [" ^ input ^ "]")
            val _ = writeTranscript 1 (fn () => input)
(*          val _ = set_nonblocking socket   XXX*)
          
          (* spinread : Time.time -> string -> string
              
           Reads repeatedly from infdFromChild.  If no output for the interval `timeout'
           (see above), raise TransactTimeout.

           Note that a looping child that keeps outputting will not trigger the timeout;
           how should we handle that?  Also: Take `timeout' as an argument?
           *)
          fun spinread cutoffTime acc =
              case Byte.bytesToString(Socket.recvVec(socket, 1)) of
                  "" =>  (* Connection closed (presumably by remote host) *)
                      String.concat (List.rev acc)
           | output => let val acc = output :: acc
                       in
                           if outputSync acc then   (* reached end of output *)
                               String.concat (List.rev acc)
                           else   (* not at end; bump timer since we got some output *)
                               spinread (Time.+ (Time.now(), timeout)) acc
                       end
          val r = spinread (Time.+ (Time.now(), timeout)) []
      in
          writeTranscript 2 (fn () => ">>>  " ^ r ^ "\n");
          r
      end

  val transact_session_INSTRUMENTED = transact_session

  fun transact_session arg1 arg2 =
      let val start = Time.now()
      in
          transact_session_INSTRUMENTED arg1 arg2
          before
          Stats.save (Time.-(Time.now(), start))
      end


  fun kill_session (ChildProcess {pid, outfdToChild, infdFromChild}) =
        let val () = Posix.IO.close outfdToChild
            val () = Posix.IO.close infdFromChild
            val (pid, exitStatus) = Posix.Process.wait ()
        in
            ()
        end
    | kill_session (RemoteProcess {socket}) =
      (Socket.shutdown(socket, Socket.NO_RECVS_OR_SENDS);
       Socket.close socket)
  
(******
  fun call {programPath, inputString} =
                                       case Posix.Process.fork() of
                                           NONE =>   (* child process *)
                                               let val () = Posix.IO.close outfdToChild
                                                   val () = Posix.IO.dup2 {old= infdToChild, new= Posix.FileSys.stdin}
                                                   val ()= Posix.IO.close infdToChild

                                                   val () = Posix.IO.close infdFromChild
                                                   val () = Posix.IO.dup2 {old= outfdFromChild, new= Posix.FileSys.stdout}
                                                   val () = Posix.IO.close outfdFromChild

                                                   val () = Posix.Process.exec (programPath, programPath :: [])
                                               in
                                                   Posix.Process.exit (Word8.fromInt 99)
                                               end
                                         | SOME child =>   (* parent process *)
                                               let val () = Posix.IO.close infdToChild
                                                   val () = Posix.IO.close outfdFromChild
                                                   val _ = set_nonblocking infdFromChild

                                                   val _ = Posix.IO.writeVec (outfdToChild, {buf=Byte.stringToBytes inputString, i=0, sz=NONE})

                                                   val output = readString infdFromChild
                                                   val _ = dprint (fn () => "OUTPUT=\n" ^ output)

                                                   val () = Posix.IO.close outfdToChild
                                                   val () = Posix.IO.close infdFromChild

                                                   val _ = dprnt "Posix.Process.wait()"
                                                   val (pid, exitStatus) = Posix.Process.wait ()
                                               in
                                                   (dprnt ("\nDONE[" ^ (Int.toString o SysWord.toInt o Posix.Process.pidToWord) pid ^ "]");
                                                    SOME "fakeresult")
                                               end
                                    end
*****)

  fun beginsWith s1 s2 = String.isPrefix s2 s1


(*
  fun call_cvc s =
      case call {programPath= "./cvcwrap",
            inputString = s} of
          NONE => NONE
        | SOME s => if beginsWith s "cvcwrap=VALID" then SOME true
              else if beginsWith s "cvcwrap=INVALID" then SOME false
                   else (print ("call_cvc protocol violation: <<\n" ^ s ^ "\n>>\n"); NONE)

  fun call_svc2 s =
      let val session = launch_session {programPath = "/usr2/svc2/bin/linux/svc2" (* "/usr0/svc-1.1/bin/svc" *) (*"/Users/jcd/svc-1.1/bin/svc" *) ,
                                        arguments= [(*"+interactive"*)]}
(*        val q = transact_session session {input= "\n", outputSync = (fn output => size output > 1)}
          val _ = print ("<1<<<"^q^"\n")
*)
          val output = transact_session session {input= s,
                                                 outputSync= makeSillyOutputSync (fn output => (print ("<<<"^output^">>>\n"); String.isSubstring "\nValid.\n" output orelse String.isSubstring "\nInvalid.\n" output))}
          val _ = kill_session session
      in
          if String.isSubstring "\nValid.\n" output then
              SOME false
          else if String.isSubstring "\nInvalid.\n" output then
              SOME true
               else NONE
      end handle TransactTimeout s => (print ("TransactTimeout (" ^ s ^ ")\n");
                                       NONE)

  fun XXX_call_svc2 s =
      case call {programPath = "./svc2wrap",
                 inputString = s} of
          NONE => NONE
        | SOME s => if beginsWith s "svc2wrap=VALID" then SOME true
              else if beginsWith s "svc2wrap=INVALID" then SOME false
                   else (print ("call_svc2 protocol violation: <<\n" ^ s ^ "\n>>\n"); NONE)

  fun call_svc1 s =
      case call {programPath = "./svc1wrap",
                 inputString = s} of
          NONE => NONE
        | SOME s => if beginsWith s "svc1wrap=VALID" then SOME true
              else if beginsWith s "svc1wrap=INVALID" then SOME false
                   else (print ("call_svc1 protocol violation: <<\n" ^ s ^ "\n>>\n"); NONE)
*)
(****
  fun XXX_call_svc1 s =
      let val session = launch_session {programPath = (* "/usr0/svc-1.1/bin/svc" *)
        (fn x => fn y => fn z => x) "/Users/jcd/svc-1.1/bin/svc" "/bin/cat" "/Users/jcd/bin/ics",
                                        arguments= []}
(*          val _ = print ("$: " ^ transact_session session {input= "\n\n", outputSync= (fn output => String.isSuffix "SVC(1)> " output)})
          val _ = print "first transaction OK\n"
*)
          val output = transact_session session {input= "quit\n"(*s*)  (*"help help.\n" *), 
                                                 outputSync= (fn output => size output > 1 (* String.isSuffix "\nSVC(2)> " output *) )}
          val _ = kill_session session
      in
          if String.isSubstring "\nValid.\n" output then
              SOME false
          else if String.isSubstring "\nInvalid.\n" output then
              SOME true
               else NONE
      end handle TransactTimeout s => (print ("TransactTimeout (" ^ s ^ ")\n");
                                       NONE)
****)

  fun connectToServer (arg as {hostname, portNumber, password, syncString}) =
     (let val session = launch_remote_session {hostname= hostname, portNumber= portNumber}
      in
          case session of
              NONE => (print ("Could not launch session ("
                              ^ hostname ^ ":" ^ Int.toString portNumber ^")\n");
                       NONE)
            | SOME session =>
                  let val result = transact_session session {input= "", outputSync= makeSillyOutputSync (String.isSubstring "How are you today?\n")}
                            val _ = dprnt ("GREETING <<<" ^ "\n" ^ result ^ ">>>")
                      val result = transact_session session {input= password ^ "\n", outputSync= makeSillyOutputSync (String.isSubstring "OK")}
                            val _ = dprnt ("RESPONSE <<<" ^ "\n" ^ result ^ ">>>")
                  in
                      SOME session
                  end
      end)
      handle _ => (print "Pipe congested\n";
                   OS.Process.sleep (Time.fromSeconds 1);
                   connectToServer arg)

  fun prep_server session syncString =
      let val _ = transact_session session {input= "", outputSync= Silly_isSuffix syncString}
      in
          ()
      end

  fun start_remote_server {hostname, portNumber, syncString} =
      let val _ = dprnt ("$ " ^ " start_remote_server ``" ^ hostname ^ ":" ^ Int.toString portNumber ^ "''\n")
          val password = "zeitgeist"
          val session = connectToServer {hostname= hostname,
                                         portNumber= portNumber,
                                         password= password,
                                         syncString= syncString}
      in
          case session of
              NONE => (print ("start_remote_server: could not connect\n");
                       NONE)
            | SOME session =>
                  (prep_server session syncString;
                   SOME session
                   before
                   print "start_remote_server succeeded\n")
      end      

  fun start_remote_ics {hostname, portNumber} =
      start_remote_server {hostname=hostname, portNumber= portNumber, syncString= "ics>  "}

  fun start_remote_cvcl {hostname, portNumber} =
      start_remote_server {hostname=hostname, portNumber= portNumber, syncString= "CVC> "}

  fun start_remote_cvc4 {hostname, portNumber} =
      start_remote_server {hostname=hostname, portNumber= portNumber, syncString= "CVC4> "}
  
  fun start_local_ics path =
      let val _ = dprnt ("$ " ^ " start_local_ics ``" ^ path ^ "''\n")
          val session = launch_session {programPath= path, arguments= []}
      in
          prep_server session "ics>  ";
          SOME session
      end

  fun start_local_cvcl path =
      let val _ = dprnt ("$ " ^ " start_local_cvcl ``" ^ path ^ "''\n")
          val session = launch_session {programPath= path, arguments= ["+int"]}
      in
          prep_server session "CVC> ";
          SOME session
      end

  fun start_local_cvc4 path =
      let val _ = dprnt ("$ " ^ " start_local_cvc4 ``" ^ path ^ "''\n")
          val session = launch_session {programPath= path,
                                        arguments= [
                                             "--interactive",
                                                           (* as of circa 2012-10-03, turning on interactive mode causes cvc4
                                                           to echo back queries *)
                                             "--incremental" 
                                       ]}
      in
          prep_server session "CVC4> ";
          SOME session
          before
          print ("Started constraint solver CVC 4 (" ^ path ^ ")\n")
      end

  fun start_local_yices path =
      let val _ = dprnt ("$ " ^ " start_local_yices ``" ^ path ^ "''\n")
          val session = launch_session {programPath= path, arguments= []}
      in
          (* don't prep the server; Yices neither reads nor writes anything, and
           prep_server expects something even if the sync string is "" *)
          SOME session
      end

  fun call_ics setupCmds finalCmd = (* XXX *)
      let val password = "zeitgeist"
          val session = connectToServer {hostname= "sweden.autonomy.ri.cmu.edu",
                                         portNumber= 1313,
                                         password= password,
                                         syncString= "ics>  "}
      in
          case session of
              NONE => (print ("call_ics: could not connect\n");
                       NONE)
            | SOME session =>
                  let fun doSetupCmds [] = ()
                        | doSetupCmds (cmd :: rest) =
                          let val _ = dprnt ("sending ``" ^ cmd ^ "''")
                              val r = transact_session session {input= cmd^"\n",
                                                                outputSync= Silly_isSuffix "ics>  "}
                          in (dprnt "(((\n"; print r; print "\n)))"; ()) end
                              val _ = transact_session session {input= "",
                                                                outputSync= Silly_isSuffix "ics>  "}
                              val _ = doSetupCmds setupCmds
val _ = dprnt ("finalCmd sending ``" ^ finalCmd ^ "''")
                              val resultString =  transact_session session {input= finalCmd^"\n",
                                                                      outputSync= Silly_isSuffix "ics>  "}
                              val _ = dprnt "<<<"
                              val _ = dprnt resultString
                              val _ = dprnt "\n>>>"
                              val result = 
                                  if String.isSubstring "\n:false\n" resultString then
                                      SOME false
                                  else if String.isSubstring "\n:true\n" resultString then
                                      SOME true
                                       else
                                           NONE
                  in
                      result
                      before
                      kill_session session
                  end
      end

  fun invade_Sweden password =
      let val session = connectToServer {hostname= "sweden.autonomy.ri.cmu.edu",
                                         portNumber= 1313,
                                         password= password,
                                         syncString= "ics>  "}
      in
          case session of
              NONE => dprnt ("error invading Sweden\n")
            | SOME session =>
                  let fun send k s =
                        let val result = transact_session session {input= s, outputSync= Silly_isSuffix "ics>  "}
                            val _ = dprnt ("<<<RESULT" ^ Int.toString k ^ "\n" ^ result ^ ">>>")
                        in
                            ()
                        end
                      val _ = send 2 "help help.\n"
                      val _ = send 3 "help help.\n"
                      val _ = send 4 "exit.\n"
                  in
                      kill_session session
                  end
      end

  fun kill_all () =
      let val sessions = !session_list
          val _ = session_list := []
      in
          (* Silently kill all sessions *)
          List.app (fn session => ((kill_session session) handle _ => ())) sessions
      end

(*  val _ = print "PIPER RE-EFFECT\n" *)

end (* functor PiperFn *)

structure Piper = PiperFn (struct end)
