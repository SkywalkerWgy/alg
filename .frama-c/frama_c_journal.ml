(* Frama-C journal generated at 18:54 the 25/06/2025 *)

exception Unreachable
exception Exception of string

[@@@ warning "-26"]

(* Run the user commands *)
let run () =
  Project.set_keep_current false;
  File.init_from_cmdline ();
  Dynamic.Parameter.String.set "-wp-cache" "update";
  Dynamic.Parameter.String.set ""
    "/home/wgy/algorithms/Benchmark/acsl-algorithms_verified";
  File.init_from_cmdline ();
  let p_interactive = Project.create "interactive" in
  Project.set_current ~on:true p_interactive;
  File.init_from_cmdline ();
  Project.set_current ~on:true (Project.from_unique_name "default");
  Project.set_current p_interactive;
  let p_interactive_2 = Project.create "interactive" in
  Project.set_current ~on:true p_interactive_2;
  Dynamic.Parameter.String.set ""
    "/home/wgy/algorithms/Benchmark/acsl-algorithms_verified";
  File.init_from_cmdline ();
  Project.set_current ~on:true p_interactive;
  Project.set_current p_interactive_2;
  Dynamic.Parameter.Int.set "-wp-timeout" 11;
  Dynamic.Parameter.Int.set "-wp-timeout" 10;
  Project.remove ~project:p_interactive_2 ();
  let p_interactive_3 = Project.create "interactive" in
  Project.set_current ~on:true p_interactive_3;
  File.init_from_cmdline ();
  Project.set_current ~on:true p_interactive;
  Project.set_current p_interactive_3;
  ()

(* Main *)
let main () =
  Journal.keep_file
     (Datatype.Filepath.of_string
     (".frama-c/frama_c_journal.ml"));
  try run ()
  with
  | Unreachable -> Kernel.fatal "Journal reaches an assumed dead code" 
  | Exception s -> Kernel.log "Journal re-raised the exception %S" s
  | exn ->
    Kernel.fatal
      "Journal raised an unexpected exception: %s"
      (Printexc.to_string exn)

(* Registering *)
let main : unit -> unit =
  Dynamic.register
    ~plugin:"Frama_c_journal.ml"
    "main"
    (Datatype.func Datatype.unit Datatype.unit)
    ~journalize:false
    main

(* Hooking *)
let () = Cmdline.run_after_loading_stage main; Cmdline.is_going_to_load ()
