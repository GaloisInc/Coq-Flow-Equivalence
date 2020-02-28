Contains a Coq formalization of flow equivalence, adapted from 

> Cortadella, Jordi, Alex Kondratyev, Luciano Lavagno, and Christos P. Sotiriou. "Desynchronization: Synthesis of asynchronous circuits from synchronous specifications." IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 25, no. 10 (2006). DOI 10.1109/TCAD.2005.860958.

The formalization is presented in the paper 

> "Formal Verification of Flow Equivalence in Desynchronized Designs"

by Jennifer Paykin, Brian Huffman, Daniel M. Zimmerman, and Peter Beerel, 
to appear at ASYNC 2020, Snowbird, Utah, USA.

## Files in this directory

* `Monad.v`: Formalization of monads, not specific to flow equivalence.
* `Base.v`: Some preliminary definitions and tactics, not specific to flow equivalence.
* `FlowEquivalence.v`: Definitions of synchronous and asynchronous execution of circuits, marked graphs, and flow equivalence.
* `RiseDecoupled.v`: Proof that the rise decoupled protocol satisfies flow equivalence.
* `FallDecoupled.v`: Proof that the fall decoupled protocol satisfies flow equivalence.
* `Desynchronization.v`: Counterexample to Cortadella et al's proof tha the desynchronization protocol satisfies flow equivalence.

## Building the project and documentation

The best way to install Coq is via [opam](https://coq.inria.fr/opam-using.html). You can then compile the sources, checking that the proofs in the files go through, by calling `make`. If the files compile with no errors, all the proofs have been verified.

`make` will also generate documentation in the `html` subdirectory, which you can explore starting from the table of contents page `html/toc.html`.

The development currently compiles with Coq 8.8.1.

To explore the development interactively, you will need to install an IDE, either [ProofGeneral](https://proofgeneral.github.io/#quick-installation-instructions) (an emacs plugin) or CoqIDE (which can also be installed using opam via the link above).

Acknwoledgement:

This material is based upon work supported by the Defense Advanced Research Projects Agency (DARPA) under Contract No. HR0011-19-C-0070. The views, opinions, and/or findings expressed are those of the author(s) and should not be interpreted as representing the official views or policies of the Department of Defense or the U.S. Government. Distribution Statement "A" (Approved for Public Release, Distribution Unlimited).
