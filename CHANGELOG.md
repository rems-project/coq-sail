Changelog
=========

master
----
* Port to `dune`

0.19
----

* New properly typed representation of sequential register state and
  register references
* Simpler definition of the `mword` bitvector type, so that it can be
  more easily replaced with the underlying library type
* Fixes for Coq 8.20

0.18
----

* Use the release version of the stdpp bitvector package
* Improved support for stdpp, in particular providing instances for
  its `EqDecision` and `Inhabited` type classes
* Simplify some function definitions
* Remove obsolete solver tactics

0.17
----

* Fixes for Coq 8.18.0 support
* Add a few minor missing built-in functions
* Make more vector functions transparent
* Add support for new Sail concurrency interface for stdpp package

Corresponds to the 0.17 Sail release.

0.16
----

First release from the separate coq-sail repository.  This makes the
packaging for opam somewhat easier.  Corresponds to the 0.16 Sail
release.
