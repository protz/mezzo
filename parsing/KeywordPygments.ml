open Printf
let () =
  try
    printf "\"\"\"\n\n";
    printf "  This file is auto-generated from Keywords by KeywordPygments.ml\n\n";
    printf "\"\"\"\n\n";
    printf "class MezzoKeywords:\n";
    printf "  keywords = [\n";
    while true do
      let line = input_line stdin in
      printf "    '%s',\n" line
    done
  with End_of_file ->
    printf "  ]\n%!"
