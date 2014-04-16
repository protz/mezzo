module type NAME = sig

  (* A type of names. *)
  type name

  (* Maps whose keys are names. *)
  module Map : sig
    type 'a t
    val empty: 'a t
    val add: name -> 'a -> 'a t -> 'a t
    val find: name -> 'a t -> 'a
    val mem: name -> 'a t -> bool
  end

  (* [fresh x] produces a new name, which serves as a replacement for the
     previous name [x]. Passing [x] to [fresh] allows it to retain some
     information, such as a printing hint, or a sort (if there are several
     sorts of names). *) (* TEMPORARY not yet implemented *)
  val fresh: unit -> name

end

module type PATTERN = sig

  (* A pattern has holes of type ['x] that stand for variable occurrences,
     holes of type ['i] that stand for an expression in the scope of the
     current binding construct, and holes of type ['o] that stand for an
     expression outside of the scope of the current binding construct. *)

  type ('x, 'i, 'o) pat

  (* The [map] operation transforms a pattern into a pattern of identical
     shape, applying the suitable user-supplied function at every
     hole. *)

  val map:
    ('x1 -> 'x2) ->
    ('i1 -> 'i2) ->
    ('o1 -> 'o2) ->
    ('x1, 'i1, 'o1) pat -> ('x2, 'i2, 'o2) pat

  (* The [fold] operation allows iterating over every hole. *)

  val fold:
    ('x -> 'a -> 'a) ->
    ('i -> 'a -> 'a) ->
    ('o -> 'a -> 'a) ->
    ('x, 'i, 'o) pat -> 'a -> 'a

end

module type EXPRESSION = sig

  (* An expression has holes of type ['x] that stand for variable occurrences
     and holes of type ['p] that stand for a pattern and signal the presence
     of a binding construct. *)

  type ('x, 'p) expr

  (* The [subst] operation transforms an expression into an expression of
     identical shape, applying the suitable user-supplied function at every
     hole. At variable holes, the user-supplied function produces a new
     expression, to be substituted for the variable. *)

  val subst:
    ('x1 -> ('x2, 'p2) expr) ->
    ('p1 -> 'p2) ->
    ('x1, 'p1) expr -> ('x2, 'p2) expr

  (* The [var] operation constructs an expression that consists of a single
     variable hole. *)

  val var: 'x -> ('x, 'p) expr

  (* The [fold] operation allows iterating over every hole. *)

  val fold:
    ('x -> 'a -> 'a) ->
    ('p -> 'a -> 'a) ->
    ('x, 'p) expr -> 'a -> 'a

end

