This repository contains a Coq formalization of flow equivalence, adapted from 

> Jordi Cortadella, Alex Kondratyev, Luciano Lavagno, and Christos P. Sotiriou. "Desynchronization: Synthesis of asynchronous circuits from synchronous specifications." IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 25, no. 10 (2006). DOI [10.1109/TCAD.2005.860958](https://dx.doi.org/10.1109/TCAD.2005.860958).

Much of this formalization is presented in the paper 

> Jennifer Paykin, Brian Huffman, Daniel M. Zimmerman, and Peter Beerel. "Formal Verification of Flow Equivalence in Desynchronized Designs." 26th IEEE International Symposium on Asynchronous Circuits and Systems (ASYNC 2020), 2020. Available as [arXiv:2004.10655](https://arxiv.org/abs/2004.10655).

The repository also contains work in progress building on the ASYNC paper.

## Files in this directory

* `Monad.v`: Formalization of monads, not specific to flow equivalence.
* `Base.v`: Some preliminary definitions and tactics, not specific to flow equivalence.
* `MarkedGraph.v`: Definition of marked graphs (a kind of Petri net)
* `Circuit.v`: Definitions of synchronous and asynchronous execution of circuits, and flow equivalence.
* `RiseDecoupled.v`: Proof that the rise decoupled protocol satisfies flow equivalence.
* `FallDecoupled.v`: Proof that the fall decoupled protocol satisfies flow equivalence.
* `Desynchronization.v`: Counterexample to Cortadella et al's proof tha the desynchronization protocol satisfies flow equivalence.
* `StateSpace.v`
  * `StateSpace/Definitions.v`: Formalization of state spaces, used to model the behavior of asynchronous controllers.
  * `StateSpace/Tactics.v`: Inversion lemmas about state spaces and related tactics.
  * `StateSpace/MarkedGraphs.v`: An embedding of marked graphs into state spaces.
  * `StateSpace/Reflection.v`: Tactics for reflection over state spaces. Currently defunct.
  * `StateSpace/RelateTrace.v`: Properties about relations between two state spaces with different domains.

* `Click/`
  * `Click/Definitions.v`: Implementation of Click controllers as state spaces.
  * `Click/Invariants.v`: Proofs of key invariants about Click controllers, and tactics for working with Click state spaces, including `step_inversion_clean`.
  * `Click/ExtraInvariants.v`: Proofs of additional invariants about Click controllers.
  * `Click/MG.v`: Marked graph refinements of Click controllers.
  * `Click/PropMarked/`
	* `Click/PropMarked/PropMarked.v`: Definition of the `prop_marked` predicate that relates markings in the Click marked graphs with states in the state space.
	* `Click/PropMarked/Step.v`: Proof of `step_implies_prop_marked`.
	* `Click/PropMarked/Outgoing.v`: Proof of `outgoing_place_not_marked`.
	* `Click/PropMarked/StepPreserved.v`: Proof of `disjoint_place_marked` and `relate_implies_marked_eps`.
  * `Click/MGProofs.v`: Proof of `MG_refines_stage` that the traces produced by the Click gate-level state space are a subset of the traces produced by the corresponding marked graph.



## Building the project and documentation

The best way to install Coq is via [opam](https://coq.inria.fr/opam-using.html). You can then compile the sources, checking that the proofs in the files go through, by calling `make`. If the files compile with no errors, all the proofs have been verified.

`make` will also generate documentation in the `html` subdirectory, which you can explore starting from the table of contents page `html/toc.html`.

The development currently compiles with Coq 8.8.1.

To explore the development interactively, you will need to install an IDE, either [ProofGeneral](https://proofgeneral.github.io/#quick-installation-instructions) (an emacs plugin) or CoqIDE (which can also be installed using opam via the link above).

## Acknowledgment

This material is based upon work supported by the Defense Advanced Research Projects Agency (DARPA) under Contract No. HR0011-19-C-0070. The views, opinions, and/or findings expressed are those of the author(s) and should not be interpreted as representing the official views or policies of the Department of Defense or the U.S. Government. Distribution Statement "A" (Approved for Public Release, Distribution Unlimited).
