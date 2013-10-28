var skip = { special: "skip" };

var tail_rec_map_data = [
  { left: [], right: [] },

  {
    left: [
      "c0 @ cell b",
      "xs @ list a",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ Cell { head: b; tail: () }",
      "xs @ list a",
    ],
    right: [
      "f @ (consumes a) -> b",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ Cell { head = c0_h; tail = c0_t }",
      "c0_h @ b",
      "xs @ list a",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
    ]
  },

  skip,

  {
    left: [
      "c0 @ Cell { head = c0_h; tail = c0_t }",
      "c0_h @ b",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "xs @ Nil",
    ]
  },

  {
    left: [
      "c0 @ Cell { head = c0_h; tail = xs }",
      "c0_h @ b",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "xs @ Nil",
    ]
  },

  {
    left: [
      "c0_h @ b",
    ],
    right: [
      "c0 @ Cons { head = c0_h; tail = xs }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "xs @ Nil",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ Cons { head: b; tail: Nil }",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "xs @ Nil",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ Cons { head: b; tail: list b }",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "xs @ Nil",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ list b",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "xs @ Nil",
    ]
  },

  {
    left: [
      "c0 @ Cell { head = c0_h; tail = c0_t }",
      "c0_h @ b",
      "xs @ Cons { head: a; tail: list a }",
    ],
    right: [
      "f @ (consumes a) -> b",
      "c0_t @ ()",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ Cell { head = c0_h; tail = c0_t }",
      "c0_h @ b",
      "h @ a",
      "t @ list a",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
    ]
  },

  {
    left: [
      "c0 @ Cell { head = c0_h; tail = c0_t }",
      "c0_h @ b",
      "h' @ b",
      "t @ list a",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
    ]
  },

  {
    left: [
      "c0 @ Cell { head = c0_h; tail = c0_t }",
      "c0_h @ b",
      "h' @ b",
      "t @ list a",
      "c1 @ Cell { head = h'; tail = c1_t }",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
    ]
  },

  {
    left: [
      "c0 @ Cell { head = c0_h; tail = c1 }",
      "c0_h @ b",
      "h' @ b",
      "t @ list a",
      "c1 @ Cell { head = h'; tail = c1_t }",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
    ]
  },

  {
    left: [
      "c0_h @ b",
      "h' @ b",
      "t @ list a",
      "c1 @ Cell { head = h'; tail = c1_t }",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
      "c0 @ Cons { head = c0_h; tail = c1 }",
    ]
  },

  {
    special: "hold",
    left: [
      "c0_h @ b",
      "t @ list a",
      "c1 @ Cell { head: b; tail: () }",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
      "c0 @ Cons { head = c0_h; tail = c1 }",
    ]
  },

  {
    special: "hold",
    left: [
      "c0_h @ b",
      "t @ list a",
      "c1 @ cell b",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
      "c0 @ Cons { head = c0_h; tail = c1 }",
    ]
  },

  {
    left: [
      "c0_h @ b",
      "c1 @ list b",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
      "c0 @ Cons { head = c0_h; tail = c1 }",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ Cons { head: b; tail: list b }",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
    ]
  },

  {
    special: "hold",
    left: [
      "c0 @ list b",
    ],
    right: [
      "xs @ Cons { head = h; tail = t }",
      "f @ (consumes a) -> b",
      "c0_t @ ()",
      "c1_t @ ()",
    ]
  },

];

var tail_rec_map_options = {
  offset: 15,
};

