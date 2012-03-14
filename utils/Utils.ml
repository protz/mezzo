let fresh_name =
  let counter = ref 0 in
  fun prefix ->
    let n = string_of_int !counter in
    counter := !counter + 1;
    prefix ^ n
;;

