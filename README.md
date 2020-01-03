Contains a Coq formalization of flow equivalence, adapted from 

> Cortadella, Jordi, Alex Kondratyev, Luciano Lavagno, and Christos P. Sotiriou. "Desynchronization: Synthesis of asynchronous circuits from synchronous specifications." IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 25, no. 10 (2006). DOI 10.1109/TCAD.2005.860958.

The formalization is presented in the paper 

> "Formal Verification of Flow Equivalence in Desynchronized Designs"

by (anonymous), in submission to ASYNC 2020.

## Files in this directory

* `Monad.v`: Formalization of monads, not specific to flow equivalence.
* `Base.v`: Some preliminary definitions and tactics, not specific to flow equivalence.
* `FlowEquivalence.v`: Definitions of synchronous and asynchronous execution of circuits, marked graphs, and flow equivalence.
* `RiseDecoupled.v`: Proof that the rise decoupled protocol satisfies flow equivalence.
* `FallDecoupled.v`: Proof that the fall decoupled protocol satisfies flow equivalence.
* `Desynchronization.v`: Counterexample to Cortadella et al's proof tha the desynchronization protocol satisfies flow equivalence.

## Installing Coq

The best way to install Coq is via [opam](https://coq.inria.fr/opam-using.html). You can then compile the sources, checking that the proofs in the files go through, by calling `make`. This will also generate html files in the `html` subdirectory, which you can explore starting from the table of contents page `html/toc.html`.

The development currently compiles with Coq 8.8.1.

To explore the development interactively, you will need to install an IDE, either [ProofGeneral](https://proofgeneral.github.io/#quick-installation-instructions) (an emacs plugin) or CoqIDE (which can also be installed using opam via the link above).
