open Printf
let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-vim" then
    try
      let file = open_in Sys.argv.(2) in
      printf "\" This file is auto-generated from %s by KeywordGenerator.ml\n" Sys.argv.(2);
      while true do
        let line = input_line file in
        if line = "##KEYWORDS##" then
          try
            while true do
              let line = input_line stdin in
              printf "syn keyword  mezzoKeyword %s\n" line
            done
          with End_of_file ->
            printf "\n"
        else
          fprintf stdout "%s\n" line
      done
    with End_of_file ->
      printf "\n%!"
  else
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
