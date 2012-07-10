open Types
open TypePrinter
open Bash

let enabled = ref false;;
let enable_trace v = enabled := v;;

let explain env x =
  if !enabled then begin
    (* Reset the screen. *)
    flush stdout; flush stderr;
    reset ();

    (* Print the current position. *)
    Hml_String.bprintf "Last checked expression: %a at %a\n"
      pnames (get_names env x)
      Lexer.p env.position;

    (* Print MOAR. *)
    Hml_String.bprintf "\n";
    Hml_String.bprintf "%a\n\n" ppermissions env;
    Hml_String.bprintf "%s\n\n" (String.make twidth '-');
    flush stdout; flush stderr;
    ignore (input_char stdin)
  end
;;
