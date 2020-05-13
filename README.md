# Formal Topology in Univalent Foundations

This is the Agda development accompanying my (upcoming) master's thesis at Chalmers
University of Technology to be titled "Formal Topology in Univalent Foundations".

The development of formal topology presented here follows an idea of Thierry Coquand [0]
to define formal topologies as posets endowed with [interaction systems][1]. The novelty
presented in this development is that the usual cover relation of formal topologies is
defined as an HIT. This seems to be necessary to avoid having to use a form of choice.

The version of the code presented in the thesis will be archived whereas this repository
(which is, as of now, mostly the same) will maintained and developed further.

## Question: what is formal topology?

Here is an answer by Giovanni Sambin [2]:

> What is formal topology? A good approximation to the correct answer is: formal topology
> is topology as developed in (Martin-Löf's) type theory.

## Overview

The main development comprises nine modules. If you are interested in reading the code, I
suggest the following order:

1. `Basis`. Definitions of foundational notions (powerset, etc).
2. `Poset`.
3. `Frame`. A rudimentary development of frames.
4. `Nucleus`. The notion of a [nucleus][3] on a frame.
5. `FormalTopology`. Definition of a formal topology as an interaction system.
6. `Cover`. The cover relation induced by the structure of a formal topology.
7. `CoverFormsNucleus`. Contains the proof that the cover relation of a formal topology is
   a nucleus on the frame of downwards-closed subsets of its underlying poset.
8. `UniversalProperty`. Contains the proof that formal topologies present frames as
   expected.
9. `CantorSpace`. The definition of the formal Cantor topology along with a proof that it
   is compact.
   
## Credits

This is joint work with Thierry Coquand, my master's thesis supervisor.

## References

0. Coquand, T. 1996. Formal Topology with Posets. http://www.cse.chalmers.se/~coquand/formal.html
2. Sambin, G. 2000. Formal Topology and Domains. Electronic Notes in Theoretical Computer Science. 35, (Jan. 2000), 177–190. DOI:https://doi.org/10.1016/S1571-0661(05)80742-X.

[1]: http://www.dcs.ed.ac.uk/home/pgh/interactive_systems.html
[3]: https://ncatlab.org/nlab/show/nucleus
