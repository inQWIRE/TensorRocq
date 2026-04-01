# TensorRocq

TensorRocq is a library for reasoning about symmetric monoidal categories (SMCs) in Rocq, presented in (our paper). The current tactics provided can automatically resolve SMC equations derivable from the axioms and rewrite modulo SMC equivalence. TensorRocq supports both [chyp](https://github.com/akissinger/chyp/tree/master)-style reasoning about abstract theories, as well as reasoning within existing theories.

For an example of abstract reasoning, see [FrobExample.v](Examples/FrobExample.v). For an example of application to an existing theory, see [VyZXExample.v](Examples/VyZXExample.v).



<!-- TODO: ## Table of Contents -->

## Setup

To compile SQIR and VOQC, you will need [Rocq](https://rocq-prover.org/) (formerly known as Coq) and [stdpp](https://gitlab.mpi-sws.org/iris/stdpp/). In order to build the examples, you will also need the [QuantumLib](https://github.com/inQWIRE/QuantumLib) and [VyZX](https://github.com/inQWIRE/VyZX) libraries. We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Rocq and `opam switch` to manage Rocq versions. We currently support Rocq **version 8.20**. If you run into errors when compiling our proofs, first check your version of Rocq (`coqc -v`).

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


*Notes*:
* We require Coq version 8.20.


<!-- TODO: ## Directory Contents -->
<!-- 
### SQIR

Definition of the SQIR language.

- DensitySem.v : Density matrix semantics for general SQIR programs.
- Equivalences.v : Verified circuit equivalences for peephole optimizations.
- ExtractionGateSet.v : Expanded gate set used for extraction.
- GateDecompositions.v : Verified optimized decompositions for CH, CU1, CU2, CU3, CCU1, CSWAP, C3X, and C4X.
- NDSem.v : Non-deterministic semantics for general SQIR programs.
- DiscreteProb.v : Utilities to describe running a quantum program and sampling from the output probability distribution.
- SQIR.v : Definition of the SQIR language.
- UnitaryOps.v : Utilities for manipulating unitary SQIR programs.
- UnitarySem.v : Semantics for unitary SQIR programs.

### VOQC

Verified transformations of SQIR programs. The optimizations and mapping routines extracted to our OCaml library ([inQWIRE/mlvoqc](https://github.com/inQWIRE/mlvoqc)) are all listed in **Main.v**. So this file is a good starting point for getting familiar with VOQC.

The rest of the files in the VOQC directory can be split into the following categories:

- Utilities
  - GateSet.v : Coq module for describing a quantum gate set.
  - IBMGateSet.v : "IBM" gate set {U1, U2, U3, CX}.
  - NonUnitaryListRepresentation.v : List representation of non-unitary SQIR programs.
  - RzQGateSet.v : "RzQ" gate set {H, X, Rzq, CX}.
  - FullGateSet.v : Full gate set {I, X, Y, Z, H, S, T, Sdg, Tdg, Rx, Ry, Rz, Rzq, U1, U2, U3, CX, CZ, SWAP, CCX, CCZ}.
  - UnitaryListRepresentation.v : List representation of unitary SQIR programs; includes utilities for manipulating program lists and gate set-independent proofs.

- Optimizations over unitary programs, inspired by those in [Qiskit](https://github.com/Qiskit/qiskit-terra) and [Nam et al. [2018]](https://www.nature.com/articles/s41534-018-0072-4)
  - ChangeRotationBasis.v : Auxiliary proof for Optimize1qGates.
  - GateCancellation.v : "Single-qubit gate cancellation" and "two-qubit gate cancellation" from Nam et al.
  - HadamardReduction.v : "Hadamard reduction" from Nam et al.
  - NotPropagation.v : "Not propagation" from Nam et al.
  - Optimize1qGates.v : [Optimize1qGates](https://qiskit.org/documentation/stubs/qiskit.transpiler.passes.Optimize1qGates.html) from Qiskit.
  - RotationMerging.v : "Rotation merging using phase polynomials" from Nam et al.

- Optimizations over non-unitary programs
  - PropagateClassical.v : Track classical states to remove redundant measurements and CNOT operations.
  - RemoveZRotationBeforeMeasure.v : Remove single-qubit z-axis rotations before measurement.

- Mapping routines
  - ConnectivityGraph.v : Utilities for describing an architecture connectivity graph. Includes graphs for linear nearest neighbor and 2D grid architectures.
  - GreedyLayout.v : Generate a layout based on the input program and architecture.
  - Layouts.v : Utilities for describing a physical <-> logical qubit mapping (i.e., layout).
  - MappingConstraints.v : Utilities for describing a program that satisfies architecture constraints.
  - MappingGateSet.v : Mapping gate set U + {CX, SWAP}, where U is an arbitrary set of single-qubit gates.
  - MappingValidation.v : Check whether two programs (which differ only in SWAP placement) are equivalent.
  - SwapRoute.v: Simple mapping for an architecture described by a directed graph.

- Experimental extensions
  - BooleanCompilation.v : Compilation from boolean expressions to unitary SQIR programs.

### examples

Examples of verifying correctness properties of quantum algorithms.

- Deutsch.v : Deutsch algorithm
- DeutschJozsa.v : Deutsch-Jozsa algorithm
- ghz/ : GHZ state preparation
- Grover.v : Grover's algorithm
- QPE.v : Simplified quantum phase estimation
- shor/ : Shor's algorithm, including general quantum phase estimation (use `make shor` to compile separately, see the [README in the shor directory](examples/shor/README.md) for more details)
- Simon.v : Simon's algorithm
- Superdense.v : Superdense coding
- Teleport.v : Quantum teleportation
- Utilities.v : Miscellaneous utilities used in multiple examples
- Wiesner.v : Wiesner's [quantum money](https://en.wikipedia.org/wiki/Quantum_money), contributed by Adrian Lehmann -->
<!-- 
## Acknowledgements

This project is the result of the efforts of many people. The primary contacts for this project are Kesha Hietala (@khieta) and Robert Rand (@rnrand). Other contributors include:
* Le Chang
* Akshaj Gaur
* Aaron Green
* Kesha Hietala
* Shih-Han Hung
* Adrian Lehmann
* Liyi Li
* Yuxiang Peng
* Robert Rand
* Kartik Singhal
* Runzhou Tao
* Finn Voichick

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040 and the Air Force Office of Scientific Research under Grant Number FA95502110051. -->

<!-- ## Citations

If you use SQIR or VOQC in your work, please cite our papers.

```
@article{hietala2021verified,
  title         = {A Verified Optimizer for {{Quantum}} Circuits},
  author        = {Hietala, Kesha and Rand, Robert and Hung, Shih-Han and Wu, Xiaodi and Hicks, Michael},
  year          = {2021},
  month         = jan,
  journal       = {Proceedings of the ACM on Programming Languages},
  volume        = {5},
  number        = {POPL},
  eid           = {37},
  pages         = {37},
  numpages      = {29},
  doi           = {10.1145/3434318},
  archiveprefix = {arXiv},
  eprint        = {1912.02250},
  url           = {https://github.com/inQWIRE/SQIR},
  abstract      = {We present VOQC, the first fully verified optimizer for quantum circuits, written using the Coq proof assistant. Quantum circuits are expressed as programs in a simple, low-level language called SQIR, a simple quantum intermediate representation, which is deeply embedded in Coq. Optimizations and other transformations are expressed as Coq functions, which are proved correct with respect to a semantics of SQIR programs. SQIR uses a semantics of matrices of complex numbers, which is the standard for quantum computation, but treats matrices symbolically in order to reason about programs that use an arbitrary number of quantum bits. SQIR's careful design and our provided automation make it possible to write and verify a broad range of optimizations in VOQC, including full-circuit transformations from cutting-edge optimizers.},
  keywords      = {programming languages, formal verification, certified compilation, quantum computing, circuit optimization},
  note          = {POPL '21}
}
```

```
@inproceedings{hietala2020proving,
  title     = {{Proving Quantum Programs Correct}},
  author    = {Hietala, Kesha and Rand, Robert and Hung, Shih-Han and Li, Liyi and Hicks, Michael},
  year      = {2021},
  month     = jun,
  booktitle = {12th International Conference on Interactive Theorem Proving (ITP 2021)},
  editor    = {Cohen, Liron and Kaliszyk, Cezary},
  publisher = {{Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik}},
  address   = {Dagstuhl, Germany},
  series    = {Leibniz International Proceedings in Informatics (LIPIcs)},
  volume    = {193},
  eid       = {21},
  pages     = {21:1--21:19},
  doi       = {10.4230/LIPIcs.ITP.2021.21},
  url       = {https://github.com/inQWIRE/SQIR},
  abstract  = {As quantum computing progresses steadily from theory into practice, programmers will face a common problem: How can they be sure that their code does what they intend it to do? This paper presents encouraging results in the application of mechanized proof to the domain of quantum programming in the context of the SQIR development. It verifies the correctness of a range of a quantum algorithms including Grover's algorithm and quantum phase estimation, a key component of Shor's algorithm. In doing so, it aims to highlight both the successes and challenges of formal verification in the quantum context and motivate the theorem proving community to target quantum computing as an application domain.},
  keywords  = {formal verification, quantum computing, proof engineering}
}
```

Alternatively, you can cite our repository using the information in [CITATION.cff](CITATION.cff). -->
