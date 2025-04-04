The Sail ISA specification language - Rocq support library
==========================================================

Overview
========

Sail is a language for describing the instruction-set architecture
(ISA) semantics of processors. Sail aims to provide a
engineer-friendly, vendor-pseudocode-like language for describing
instruction semantics. It is essentially a first-order imperative
language, but with lightweight dependent typing for numeric types and
bitvector lengths, which are automatically checked using Z3. It has
been used for several papers, available from
<http://www.cl.cam.ac.uk/~pes20/sail/>.
<p>

This repository contains the Rocq support library for models produced
by Sail for the [Rocq theorem prover](https://rocq-prover.org/)(
previously known as Coq). The
[main Sail repository](https://github.com/rems-project/sail) contains
the Sail tool for processing Sail specifications and translating them
into Rocq.

Installation
============

We suggest using the [opam package manager](https://opam.ocaml.org/)
if you also used it to install Rocq.  See [the instructions on using
opam with Rocq](https://rocq-prover.org/docs/installing-rocq) for more
information.  There are two variants which use different bitvector
libraries:

* The `coq-sail-stdpp` package uses the [stdpp
  library's](https://gitlab.mpi-sws.org/iris/stdpp) bitvector package.
  This is the default, but you can also use the `--coq-lib-style
  stdpp` option with Sail to target this package.
* The `coq-sail` package depends on the `coq-bbv` package
  for its implementation of bitvectors.  Use the `--coq-lib-style bbv`
  option with Sail to target this package.  Note that the new Sail
  concurrency interface isn't supported when targeting bbv at the
  moment; please get in touch if you need this.

It's also possible to build the libraries locally with dune. You need to install
either `coq-bbv` or `coq-stdpp-bitvector`, and then respectively
run `dune build @bbv` or `dune build @stdpp`. `dune build` alone will build both
of them. You can run very bare-bones tests for the stdpp version with
`dune build @runtest`

Licensing
=========

The library has the same licensing terms as the main Sail tool.  These
can be found in [LICENSE](LICENSE).

## Funding

This work was partially supported by the UK Government Industrial Strategy Challenge Fund (ISCF) under the Digital Security by Design (DSbD) Programme, to deliver a DSbDtech enabled digital platform (grant 105694).
This project has received funding from the European Research Council
(ERC) under the European Union’s Horizon 2020 research and innovation programme (grant agreement No 789108, ELVER).
This work was partially supported by EPSRC grant EP/K008528/1 <a href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous Engineering for
  Mainstream Systems</a>,
an ARM iCASE award, and EPSRC IAA KTF funding.
This work was partially supported by donations from Arm and Google.
Approved for public release; distribution is unlimited. This research
is sponsored by the Defense Advanced Research Projects Agency (DARPA)
and the Air Force Research Laboratory (AFRL), under contracts
FA8750-10-C-0237 ("CTSRD") and FA8650-18-C-7809 ("CIFV"). The views,
opinions, and/or findings contained in these articles OR presentations are
those of the author(s)/presenter(s) and should not be interpreted as
representing the official views or policies of the Department of
Defense or the U.S. Government.



