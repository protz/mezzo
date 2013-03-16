open Printf
let () =
  try
    printf "(* This file is auto-generated from Keywords by KeywordGenerator.ml *)\n";
    printf "open Grammar\n";
    printf "let keywords = [\n";
    while true do
      let line = input_line stdin in
      printf "  \"%s\", %s;\n" line (String.uppercase line)
    done
  with End_of_file ->
    printf "]\n%!"
