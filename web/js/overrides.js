function caml_ml_output (chan, buf, start, len) {
  var s = buf.toJsString();
  mezzo_ui_log(s.substr(start, len));
}
