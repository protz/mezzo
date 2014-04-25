//Provides: caml_sys_exit
function  caml_sys_exit(code){
  joo_global_object.mezzo.returnCode = code;
}

// //Provides: caml_wrap_exception
// //Requires: caml_global_data,MlWrappedString,caml_named_value
// function caml_wrap_exception(e) {
//   if(e instanceof Array) return e;
//   //Stack_overflow: chrome, safari
//   if(e instanceof joo_global_object.Error)
//     return [0,caml_named_value("jsError"),e];
//   //fallback: wrapped in Failure
//   return [0,caml_global_data[3],new MlWrappedString (String(e))];
// }

//Provides: caml_fs_file_content
//Requires: MlStringFromArray, caml_fs_content, caml_make_path, MlFile
//Requires: caml_raise_not_found
function caml_fs_file_content(name) {
  var path = caml_make_path(name);
  var f = caml_fs_content(path);
  if(f instanceof MlFile)
    return new MlStringFromArray(f.content());
  caml_raise_not_found();
}
