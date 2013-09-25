Mezzo, a programming language with permissions
==============================================

Please see the 
[website](http://protz.github.io/mezzo) for more information, including
documentation, papers, blog posts, and even youtube videos.


Compiling
---------

In order to compile, Mezzo requires:

- OCaml 4.01.0
- a properly-working ocamlfind command,
- the following packages: menhir, yojson, ulex, pprint, functory, fix

We recommend OPAM <http://opam.ocamlpro.com> to easily install
these dependencies. Once the dependencies are met, just run:

```
make
```


Running Mezzo
-------------

```
./mezzo --help
```


Running tests
-------------

```
make test
```
