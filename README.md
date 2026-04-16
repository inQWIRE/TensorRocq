# TensorRocq

TensorRocq is a library for reasoning about symmetric monoidal categories (SMCs) in Rocq, presented in (our paper). The current tactics provided can automatically resolve SMC equations derivable from the axioms and rewrite modulo SMC equivalence. TensorRocq supports both [chyp](https://github.com/akissinger/chyp/tree/master)-style reasoning about abstract theories, as well as reasoning within existing theories.

For an example of abstract reasoning, see [FrobExample.v](Examples/FrobExample.v). For an example of application to an existing theory, see [VyZXExample.v](Examples/VyZXExample.v).



<!-- TODO: ## Table of Contents -->

## Setup

To compile TensorRocq, you will need [Rocq](https://rocq-prover.org/) (formerly known as Coq) and [stdpp](https://gitlab.mpi-sws.org/iris/stdpp/). In order to build the examples, you will also need the [QuantumLib](https://github.com/inQWIRE/QuantumLib) and [VyZX](https://github.com/inQWIRE/VyZX) libraries. We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Rocq and `opam switch` to manage Rocq versions. We currently support Rocq **versions 8.20–9.1** for TensorRocq, and version 8.20 for the examples. If you run into errors when compiling our proofs, first check your version of Rocq (`coqc -v`).

Assuming you have opam and Rocq installed (following the instructions in the link above), follow the steps below to set up your environment to use TensorRocq.

### Installing TensorRocq

First, install [stdpp](https://gitlab.mpi-sws.org/iris/stdpp/) through opam.

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-stdpp
```

Then, TensorRocq can be installed through opam.

```bash
opam pin -y rocq-tensors https://github.com/inQWIRE/tensor-rocq.git
```

Alternatively, to use a local installation, clone the repository and run the following within the directory.

```bash
opam pin -y rocq-tensors .
```

After either command, TensorRocq can be imported and used for abstract reasoning (see [FrobExample.v](Examples/FrobExample.v)) or reasoning within existing projects (see [VyZXExample.v](Examples/VyZXExample.v)).



### Building Examples

Once TensorRocq is installed as above, follow the steps below to build the examples.

First, install [QuantumLib](https://github.com/inQWIRE/QuantumLib) through opam.

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib
```

Then install [SQIR and VOQC](https://github.com/inQWIRE/SQIR) and [VyZX](https://github.com/inQWIRE/VyZX).

```bash
opam pin -y coq-sqir https://github.com/inQWIRE/SQIR.git
opam pin -y coq-voqc https://github.com/inQWIRE/SQIR.git
opam pin -y coq-vyzx https://github.com/inQWIRE/VyZX.git
```

Finally, run `make examples`.



### How to use TensorRocq

In order to use TensorRocq, we provide two tutorials. The first tutorial is given by the file `Examples/FrobExample.v`, where we walk through building a theory in TensorRocq and using our string diagram rewrites to prove statements of this theory. We refer to this as an ``axiomatized'' method, as we allow users to define their own collection of rules and use TensorRocq to rewrite the string diagram terms.

The second tutorial is given by the file `Examples/VyZXExample.v`, where we show how to apply TensorRocq to existing projects. We do this through implementing a string diagram rewrite tactic for the [VyZX](https://github.com/inQWIRE/VyZX) library. This process involves showing the VyZX project can be given semantics based on tensors as well as showing we can translate the inductive structures present in VyZX into our APROPs. Once done, this allows hypergraph rewriting to be used in statements in the VyZX project that do not involve APROP statements, allowing for the blending of string diagram rewriting with traditional syntactic rewrites.


*Notes*:
* We require Coq versions 8.20–9.1, and version 8.20 for the examples

