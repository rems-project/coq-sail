The Sail ISA specification language - Coq support library
=========================================================

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

This repository contains the Coq support library for models produced
by Sail for the [Coq theorem prover](https://coq.inria.fr/).  The
[main Sail repository](https://github.com/rems-project/sail) contains
the Sail tool for processing Sail specifications and translating them
into Coq.

Installation
============

We suggest using the [opam package manager](https://opam.ocaml.org/)
if you also used it to install Coq.  See [the instructions on using
opam with Coq](https://coq.inria.fr/opam-using.html) for more
information.  The `coq-sail` package depends on the `coq-bbv` package
for its implementation of bitvectors.

It's also possible to build the library locally without opam using the
Makefile in the `src` directory.  You can also change the bitvector
library used by changing the `src/MachineWord.v` symbolic link.

An opam package is also available using the stdpp-unstable bitvector
library.  It changes the Coq library name so that it can be installed
alongside the BBV version, so references to `Sail` in the models
should be replaced by `SailStdpp`.  Sail can do this when generating
Coq output using the arguments `-coq_alt_modules SailStdpp.Base
-coq_alt_modules SailStdpp.Real`.

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



