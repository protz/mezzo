//Provides: caml_ml_output
function caml_ml_output (chan, buf, start, len) {
  var s = buf.toJsString();
  mezzo_ui.log(s.substr(start, len), true);
}

//Provides: caml_ml_output_char
function caml_ml_output_char (chan, ch) {
  mezzo_ui.log_char(ch);
}

//Provides: caml_sys_const_big_endian
function caml_sys_const_big_endian() {
  return false;
}

//Provides: caml_sys_const_word_size
function caml_sys_const_word_size() {
  // Since the browser is 32-bit, I assume?
  return 32;
}

//Provides: caml_sys_const_ostype_unix
function caml_sys_const_ostype_unix() {
  return true;
}

//Provides: caml_sys_const_ostype_win32
function caml_sys_const_ostype_win32() {
  return false;
}

//Provides: caml_sys_const_ostype_cygwin
function caml_sys_const_ostype_cygwin() {
  return false;
}

//Provides: caml_ml_input
function caml_ml_input () {
  console.log("Not implemented: caml_ml_input!");
  return 0;
}

//Provides: caml_ml_input_char
function caml_ml_input_char () {
  console.log("Not implemented: caml_ml_input_char!");
  return 0;
}

//Provides: caml_ml_input_scan_line
function caml_ml_input_scan_line () {
  console.log("Not implemented: caml_ml_input_scan_line!");
  return 0;
}

//Provides: caml_sys_file_exists
function caml_sys_file_exists (file) {
  var f = file.toJsString();
  return mezzo_fs.exists(f);
}

//Provides: caml_sys_getcwd
function caml_sys_getcwd () {
  return new MlString("/");
}
