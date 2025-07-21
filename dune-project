(lang dune 3.8)
(name coq-sail)
(using coq 0.8)

(source (github rems-project/coq-sail))
(homepage http://www.cl.cam.ac.uk/~pes20/sail/)
(documentation https://github.com/rems-project/sail)
(license "BSD-2-Clause")
(authors
  "Alasdair Armstrong"
  "Thomas Bauereiss"
  "Brian Campbell"
  "Shaked Flur"
  "Jonathan French"
  "Kathy Gray"
  "Robert Norton"
  "Christopher Pulte"
  "Peter Sewell"
  "Mark Wassell"
)
(maintainers "Sail Devs <cl-sail-dev@lists.cam.ac.uk>")
(version 0.19.1)

(package
 (name coq-sail)
 (synopsis "Support library for Sail, a language for describing the instruction semantics of processors")
 (description
   "The support library for instruction-set semantics generated from Sail.
Sail is a language for describing the instruction-set
architecture (ISA) semantics of processors. Sail aims to provide a
engineer-friendly, vendor-pseudocode-like language for describing
instruction semantics. It is essentially a first-order imperative
language, but with lightweight dependent typing for numeric types and
bitvector lengths, which are automatically checked using Z3. It has
been used for several papers, available from
http://www.cl.cam.ac.uk/~pes20/sail/.
The Sail tool can be found in main opam repository.")
 (depends
  (coq (>= 8.16.0))
  (coq-bbv (>= 1.3))
 )
 (conflicts (sail (<> :version)))
 (tags
   ("logpath:Sail"
   "category:Computer Science/Semantics and Compilation/Semantics"))
)

(package
 (name coq-sail-stdpp)
 (synopsis "Support library for Sail, a language for describing the instruction semantics of processors, using stdpp bitvectors")
 (description
   "The support library for instruction-set semantics generated from Sail.
Sail is a language for describing the instruction-set
architecture (ISA) semantics of processors. Sail aims to provide a
engineer-friendly, vendor-pseudocode-like language for describing
instruction semantics. It is essentially a first-order imperative
language, but with lightweight dependent typing for numeric types and
bitvector lengths, which are automatically checked using Z3. It has
been used for several papers, available from
http://www.cl.cam.ac.uk/~pes20/sail/.
The Sail tool can be found in main opam repository.")
 (depends
  (coq (>= 8.18))
  (coq-stdpp-bitvector (>= 1.10.0))
 )
 (conflicts (sail (<> :version)))
 (tags
  ("logpath:Sail"
    "category:Computer Science/Semantics and Compilation/Semantics"))
)

; Don't generate opam files for the moment because they've been altered to work
; around dune's lack for support for the Stdlib change.
; (generate_opam_files)
