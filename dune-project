(lang dune 2.8)
(name rocq-tensors)
(version 0.1.0)
(using coq 0.2)

(generate_opam_files true)

(license MIT)
(authors "inQWIRE")
(maintainers "inQWIRE Developers")
(source (github inQWIRE/tensor-rocq))
(homepage https://github.com/inQWIRE/tensor-rocq/)
(bug_reports https://github.com/inQWIRE/tensor-rocq/issues)

(package
 (name rocq-tensors)
 (synopsis "Rocq library providing hypergraph rewriting using tensor semantics")
 (homepage https://github.com/inQWIRE/tensor-rocq/)
 (bug_reports https://github.com/inQWIRE/tensor-rocq/issues)
 (depends (rocq-stdpp (>= 0)))
)

(package
  (name rocq-tensors-examples)
  (synopsis "Examples of rewriting PROPs using rocq-tensors")
  (depends 
    (rocq-tensors (>= 0.1.0))
    )
  )
