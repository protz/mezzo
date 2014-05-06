open TypeCore

let pinconsistency (b: Buffer.t)(i: inconsistency): unit =
  Buffer.add_string b 
    (match i with
    | Consistent -> "(consistent)"
    | FailAnnot -> "failure"
    | ExclusivePerms _ -> "exclusive permission"
    | DistinctDatacon (_, _) -> "distinct datatype constructors"
    | TupleArity (_,_) -> "distinct arity of tuples")
;;
