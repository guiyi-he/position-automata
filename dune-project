(lang dune 3.14)

(name position-automata)

(generate_opam_files true)

(using coq 0.8)

(authors "Linden development")

(package
 (name position-automata)
 (synopsis "Position automata for regular expressions in Coq")
 (depends
  (coq (= 8.18.0))
  linden
  (warblre (= 0.1.0))))
