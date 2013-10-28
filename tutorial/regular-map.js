var skip = { special: "skip" };

var tail_rec_map_data = [
  { left: [], right: [] },

  {
    left: [
      "xs @ list a",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  skip,

  {
    left: [
      "xs @ Cons { head: a; tail: list a }",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  {
    special: "hold",
    left: [
      "h @ a",
      "t @ list a",
    ],
    right: [
      "f @ (consumes a) -> b",
      "xs @ Cons { head = h; tail = t }",
    ]
  },

  {
    left: [
      "h' @ b",
      "t @ list a",
    ],
    right: [
      "f @ (consumes a) -> b",
      "xs @ Cons { head = h; tail = t }",
    ]
  },

  {
    left: [
      "h' @ b",
      "t' @ list b",
    ],
    right: [
      "f @ (consumes a) -> b",
      "xs @ Cons { head = h; tail = t }",
    ]
  },

  {
    left: [
      "h' @ b",
      "t' @ list b",
    ],
    right: [
      "f @ (consumes a) -> b",
      "xs @ Cons { head = h; tail = t }",
      "ret @ Cons { head = h'; tail = t' }",
    ]
  },

  {
    special: "hold",
    left: [
      "ret @ Cons { head: b; tail: list b }",
    ],
    right: [
      "f @ (consumes a) -> b",
      "xs @ Cons { head = h; tail = t }",
    ]
  },

  {
    special: "hold",
    left: [
      "ret @ list b",
    ],
    right: [
      "f @ (consumes a) -> b",
      "xs @ Cons { head = h; tail = t }",
    ]
  },

  {
    left: [
      "xs @ Nil",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  {
    left: [
      "xs @ Nil",
      "ret = xs",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  {
    special: "hold",
    left: [
      "ret @ Nil",
      "ret = xs",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  {
    special: "hold",
    left: [
      "ret @ list b",
      "ret = xs",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

];

var tail_rec_map_options = {
  offset: 2,
};

