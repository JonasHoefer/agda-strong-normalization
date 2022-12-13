# Strong Normalization of the STLC in Agda [![CI](https://github.com/JonasHoefer/agda-strong-normalization/actions/workflows/ci.yml/badge.svg)](https://github.com/JonasHoefer/agda-strong-normalization/actions/workflows/ci.yml)

This repository contains a proof that the simply typed lambda calculus is strongly normalizing im [Agda][software/agda].
The proof uses an approach using a logical predicate.
This version is mostly based on work by Altenkirch et al.
We use an intrinsically-typed de Bruijn representation originally due to [Altenkirch and Reus][paper/altenkirch99].
A rendered version of the files can be found [here](https://jonashoefer.github.io/agda-strong-normalization/STLC.html).


# References

- [Thorsten Altenkirch, Bernhard Reus, Monadic Presentations of Lambda Terms Using Generalized Inductive Types. CSL 1999][paper/altenkirch99]
- [Thorsten Altenkirch, A Formalization of the Strong Normalization Proof for System F in LEGO. TLCA 1993][paper/altenkirch93]
- [Thorsten Altenkirch, Constructions, inductive types and strong normalization. University of Edinburgh, UK][thesis/altenkirch]


# Software

- [Agda][software/agda], Version 2.6.2.2
- [Agda Standard Library][software/agda-stdlib]


[paper/altenkirch99]:
  http://www.cs.nott.ac.uk/~psztxa/publ/csl99.pdf
  "Thorsten Altenkirch, Bernhard Reus, Monadic Presentations of Lambda Terms Using Generalized Inductive Types. CSL 1999"

[paper/altenkirch93]:
  http://www.cs.nott.ac.uk/~psztxa/publ/tlca93.pdf
  "Thorsten Altenkirch, A Formalization of the Strong Normalization Proof for System F in LEGO. TLCA 1993"

[thesis/altenkirch]:
  http://www.cs.nott.ac.uk/~psztxa/publ/phd93.pdf
  "Thorsten Altenkirch, Constructions, inductive types and strong normalization. University of Edinburgh, UK"

[software/agda]:
  https://wiki.portal.chalmers.se/agda/Main/Download
  "The Agda Wiki — Downloads"

[software/agda-stdlib]:
  https://wiki.portal.chalmers.se/agda/Libraries/StandardLibrary
  "The Agda Wiki — Standard Library"
