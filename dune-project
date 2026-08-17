(lang dune 3.11)
(name sisal)

(using menhir 2.1)

(package
 (name sisal)
 (synopsis "Sisal 2.0 to IF1 / C++23 Compiler")
 (description "A modern Sisal compiler implementing rank-polymorphic dense arrays (dope vectors), side-effect monad ordering, and C++23 code generation.")
 (authors "Ram")
 (depends
  (ocaml (>= 4.14.0))
  (dune (>= 3.11))
  (menhir (>= 20211230))
  (re (>= 1.10.0))))

(generate_opam_files true)
