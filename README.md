Mezzo, a programming language with permissions
==============================================

Please see the 
[website](http://protz.github.io/mezzo) for more information, including
documentation, papers, blog posts, and even youtube videos.

Installing Mezzo
----------------

Mezzo is now in OPAM, just run `opam install mezzo`.


Learning Mezzo
--------------

There's a [sample projet](https://github.com/protz/mezzo-sample-project/) for
you to get started, and a [tutorial](http://protz.github.io/mezzo/tutorial/)
that's nowhere near finished. We have a [website](http://protz.github.io/mezzo/)
with more research-y material.


Hacking on Mezzo
----------------

If you want to hack on the compiler itself, you need:

- OCaml 4.01.0
- a properly-working ocamlfind command,
- the following packages: menhir, yojson, ulex, pprint, functory, fix, js_of_ocaml

We recommend [OPAM](http://opam.ocamlpro.com) to easily install
these dependencies. Once the dependencies are met, just run:

```
make
```

This configures Mezzo and builds it locally. That is, you are *not* expected to
use `make install`. The Mezzo executable exists locally, and you can run it from
there, possibly adding the Mezzo source directory to your PATH.

From there on you can hack on the compiler, write new modules in `stdlib`, etc.
Our [website](http://protz.github.io/mezzo/) has online links with the
auto-generated documentation for the compiler.
