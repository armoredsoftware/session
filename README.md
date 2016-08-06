# session

Dependencies:
-Emacs Proof General (tested under Version 4.3pre150930): (https://proofgeneral.github.io/)
-Coq (tested under version 8.5pl1):  https://coq.inria.fr/

Compilation instructions:
-type `make`
-open the desired .v file and step through the Coq definitions and
proofs interactively!

Crypto.v:  A dependently typed model of perfect cryptography.
Includes the \texttt{message} Inductive type.

ProtoRep.v:  The protocol representation.  Includes the
implentation of Session Types (\texttt{protoType} Inductive type), the
protocol expressions that inhabit them (\texttt{protoExp} Inductive
type), and the \texttt{Dual} definition.

ProtoStateSemantics.v:  Operational semantics and proofs about it.

Examples.v:  Example protocols and proofs of specialized properties.

SfLib.v:  Library from Software Foundations
(https://www.cis.upenn.edu/~bcpierce/sf/current/index.html).

CpdtTactics.v:  Library from Certified Programming with Dependent Types (http://adam.chlipala.net/cpdt/).
