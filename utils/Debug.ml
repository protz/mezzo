open Types
open TypePrinter
open Bash

let enabled = ref false;;
let enable_trace b = enabled := b;;

type op =
  | FunctionCall of point * point
  | FunctionArg of point
  | AfterFunctionCall of typ

let stack = ref [];;
let push x = stack := x :: !stack;;
let pop () = stack := List.tl !stack;;

let pfold buf (env, p) =
  match Permissions.fold env p with
  | Some t ->
      Buffer.add_string buf "[[";
      ptype buf (env, t);
      Buffer.add_string buf "]]";
  | None ->
      ppermission_list buf (env, p)

let string_of_op env = function
  | FunctionCall (f, x) ->
      Hml_String.bsprintf "%s%a%s function call between\n  %a : %a\n  %a : %a"
        colors.red Lexer.p env.position colors.default
        pnames (get_names env f)
        pfold (env, f)
        pnames (get_names env x)
        pfold (env, x)

  | FunctionArg x ->
      Hml_String.bsprintf "%s%a%s got the good type for the argument\n  %a : %a"
        colors.red Lexer.p env.position colors.default
        pnames (get_names env x)
        pfold (env, x)

  | AfterFunctionCall t ->
      Hml_String.bsprintf "%s%a%s function call finished, return type is\n  %a"
        colors.red Lexer.p env.position colors.default
        ptype (env, t)
;;


let flush_break () =
  flush stdout; flush stderr;
  ignore (input_char stdin)
;;


let trace env op =
  if !enabled then begin
    push op;
    flush_break ();
    reset ();
    List.iter (fun op -> Hml_String.bprintf "%s\n" (string_of_op env op)) (List.rev !stack);
    Hml_String.bprintf "\n\n";
    Hml_String.bprintf "%a\n\n" ppermissions env;
    Hml_String.bprintf "%s\n\n" (String.make twidth '-');
    flush_break ()
  end
;;

let clear_trace () = if !enabled then pop ();;

let trace_one env op =
  if !enabled then begin
    trace env op;
    clear_trace ()
  end
