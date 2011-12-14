module TyCon = struct
  (* The name is here for printing purposes only. The “real” information is
   * contained in the global index. *)
  type t = Variable.name * Types.index
  let compare = fun (_, x) (_, y) -> compare x y
  let show (name, _) = Variable.print name
end

module MD = ModeDeduction.Make(Mode)(TyCon)
open MD

type facts = rule list

let analyze_data_types
    (env: Types.env)
    : facts =
      []

let string_of_facts facts =
  ""
