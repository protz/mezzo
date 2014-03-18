function caml_sys_const_big_endian() {
  return false;
}

function caml_sys_const_word_size() {
  // Since the browser is 32-bit, I assume?
  return 32;
}

function caml_sys_const_ostype_unix() {
  return true;
}

function caml_sys_const_ostype_win32() {
  return false;
}

function caml_sys_const_ostype_cygwin() {
  return false;
}

function caml_ml_channel_size () {
  console.log("Not implemented: caml_ml_channel_size!");
}

function caml_ml_close_channel () {
  console.log("Not implemented: caml_ml_close_channel!");
}

function caml_ml_input () {
  console.log("Not implemented: caml_ml_input!");
}

function caml_ml_input_char () {
  console.log("Not implemented: caml_ml_input_char!");
}

function caml_ml_input_scan_line () {
  console.log("Not implemented: caml_ml_input_scan_line!");
}

function caml_ml_output_char () {
  console.log("Not implemented: caml_ml_output_char!");
}

function caml_ml_seek_in () {
  console.log("Not implemented: caml_ml_seek_in!");
}

function caml_sys_chdir () {
  console.log("Not implemented: caml_sys_chdir!");
}

function caml_sys_close () {
  console.log("Not implemented: caml_sys_close!");
}

function caml_sys_exit () {
  console.log("Not implemented: caml_sys_exit!");
}

function caml_sys_file_exists () {
  console.log("Not implemented: caml_sys_file_exists!");
}

function caml_sys_getcwd () {
  return new MlString("- toplevel");
}

function caml_sys_is_directory () {
  console.log("Not implemented: caml_sys_is_directory!");
}

function caml_sys_open () {
  console.log("Not implemented: caml_sys_open!");
}

function caml_sys_read_directory () {
  console.log("Not implemented: caml_sys_read_directory!");
}

function caml_sys_remove () {
  console.log("Not implemented: caml_sys_remove!");
}

function caml_sys_system_command () {
  console.log("Not implemented: caml_sys_system_command!");
}

function re_replacement_text () {
  console.log("Not implemented: re_replacement_text!");
}

function re_search_forward () {
  console.log("Not implemented: re_search_forward!");
}

function unix_close () {
  console.log("Not implemented: unix_close!");
}

function unix_dup2 () {
  console.log("Not implemented: unix_dup2!");
}

function unix_execv () {
  console.log("Not implemented: unix_execv!");
}

function unix_execvp () {
  console.log("Not implemented: unix_execvp!");
}

function unix_fork () {
  console.log("Not implemented: unix_fork!");
}

function unix_inet_addr_of_string () {
  console.log("Not implemented: unix_inet_addr_of_string!");
}

function unix_isatty () {
  console.log("Not implemented: unix_isatty!");
}

function unix_pipe () {
  console.log("Not implemented: unix_pipe!");
}

function unix_set_close_on_exec () {
  console.log("Not implemented: unix_set_close_on_exec!");
}
