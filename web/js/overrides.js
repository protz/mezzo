function caml_ml_output (chan, buf, start, len) {
  var s = buf.toJsString();
  console.log("On chan "+chan+": "+s);
  mezzo_ui_log(s.substr(start, len));
}
