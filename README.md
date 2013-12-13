Mezzo, a programming language with permissions
==============================================

Please see the 
[website](http://protz.github.io/mezzo) for more information, including
documentation, papers, blog posts, and even youtube videos.


Pre-requisites
--------------

In order to compile, Mezzo requires:

- OCaml 4.01.0
- a properly-working ocamlfind command,
- the following packages: menhir, yojson, ulex, pprint, functory, fix

We recommend OPAM <http://opam.ocamlpro.com> to easily install
these dependencies. Once the dependencies are met, just run:


OPAM
----

Mezzo is available in OPAM, so we recommend using the tool to get Mezzo.


Configuration
-------------

The first option is to type:

```
make
```

straight away. This configures Mezzo and builds it locally. That is, you are
*not* expected to use `make install`. The Mezzo executable exists locally, and
you can run it from there, possibly adding the Mezzo source directory to your
PATH.

The second option consists in running:

```
./configure
make
make install
```

This will set up and install the Mezzo runtime libraries using ocamlfind.


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
