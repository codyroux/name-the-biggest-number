# name-the-biggest-number

The point of this repository is to allow people to submit contenders for the title of **biggest number**.

The idea of this competition is described by Scott Aaronson [here](https://www.scottaaronson.com/writings/bignumbers.html), but generally this is a pretty active area of recreational mathematics and a *lot* of ressources can be found [herabouts](https://googology.wikia.org/wiki/Googology_Wiki).

This repository adds 2 rather large caveats to the process:

1) The numbers described must be *constructive*: no Busy Beavers or similar shennanigans! All numbers named must be computable *in principle* (more on this later).

2) The numbers submitted must be **formally described** in the Coq specification system, along with a **formal proof** that they are larger than the current contender for largest number.

A few base rules:

- The definition of the number must take no more than 15 seconds to type-check using `coqc` on a "reasonable" machine.

- The proof that the number is larger than the current contender should take no more than 1 minute to typecheck, though I might update this as events warrent.

- No axioms! Libraries may be included if needed, but please try to stick to widely used ones.

- Submittions are made by making a PR that adds to the file `Contender.v`, according to the format outlined by that file (your number should be a definition named `contender_N`, and the proof of soundness `contender_(N-1)_lt_contender_N`.

- No shennanigans! Though I might have an honorable mention category if you can really fool me.
