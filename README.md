# session

Dependencies:
* Emacs Proof General (tested under Version 4.3pre150930): (https://proofgeneral.github.io/)
* Coq (tested under version 8.5pl1):  https://coq.inria.fr/
* In place of the two dependencies above, CoqIDE(https://coq.inria.fr/download) is a bundle of an IDE and the Coq compiler.  The proofs have NOT been tested on CoqIDE yet, so the proofs may require some modification.  Use at your own risk.  Proof General and Coq with the versions listed above are recommended to be sure the proofs compile.

Compilation instructions:
1. type `make`
2. open the desired .v file and step through the Coq definitions and
proofs interactively!

Crypto.v:  A dependently typed model of perfect cryptography.
Includes the message Inductive type.

ProtoRep.v:  The protocol representation.  Includes the
implentation of Session Types (protoType Inductive type), the
protocol expressions that inhabit them (protoExp Inductive
type), and the Dual definition.

ProtoStateSemantics.v:  Operational semantics and proofs about it.

Examples.v:  Example protocols and proofs of specialized properties.

SfLib.v:  Library from Software Foundations
(https://www.cis.upenn.edu/~bcpierce/sf/current/index.html).

CpdtTactics.v:  Library from Certified Programming with Dependent Types (http://adam.chlipala.net/cpdt/).
