//Provides: caml_sys_exit
function  caml_sys_exit(code){
  joo_global_object.mezzo.returnCode = code;
}
