(lang dune 3.21)
; As long as there is just one package dune requires that the project must have the same name
(name rocq-sail-stdpp)
(using rocq 0.11)

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
(version 0.20.2)

; We've dropped the BBV version of the library for now.
;
;(package
; (name rocq-sail)
; (synopsis "Support library for Sail, a language for describing the instruction semantics of processors")
; (description
;   "The support library for instruction-set semantics generated from Sail.
;Sail is a language for describing the instruction-set
;architecture (ISA) semantics of processors. Sail aims to provide a
;engineer-friendly, vendor-pseudocode-like language for describing
;instruction semantics. It is essentially a first-order imperative
;language, but with lightweight dependent typing for numeric types and
;bitvector lengths, which are automatically checked using Z3. It has
;been used for several papers, available from
;http://www.cl.cam.ac.uk/~pes20/sail/.
;The Sail tool can be found in main opam repository.")
; (depends
;  (rocq (>= 9.0))
;  (coq-bbv (>= 1.3))
; )
; (conflicts (sail (<> :version)))
; (tags
;   ("logpath:Sail"
;   "category:Computer Science/Semantics and Compilation/Semantics"))
;)

(package
 (name rocq-sail-stdpp)
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
  (rocq-core (>= 9.0))
  (rocq-stdpp-bitvector (>= 1.13.0))
 )
 (conflicts (sail (<> :version)))
 (tags
  ("logpath:Sail"
    "category:Computer Science/Semantics and Compilation/Semantics"))
)

(generate_opam_files)
