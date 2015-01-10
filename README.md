hott-limits
===========

A formalization of (homotopy) limits in Homotopy Type Theory, over the Coq HoTT library, as presented in the paper *Homotopy limits in Type Theory.*

Authors: Jeremy Avigad, Krzysztof Kapulkin, Peter LeFanu Lumsdaine.

1. Overview
2. Getting started
3. Organization
4. Versions and compatibility
5. Licensing

# Overview #

This library develops (homotopy) limits of diagrams of types over graphs, working in Coq over [the HoTT library](http://www.github.com/HoTT/HoTT).  In particular, we present pullbacks and their basic theory (including concrete constructions, universal properties, examples, and the two pullback lemma), some similar basic theory for general diagrams over graphs (including the construction of a general limit from products and equalisers), and one application, the long exact sequence associated to a fibratoin.

To balance the competing demands of an academic publication and a software library, this repository includes both stable and evolving versions of the library: roughly, a stable branch `v1` accompanying the paper, and an evolving branch `master`.  Precisely, the tag `MSCS` on the `v1` branch will be permanently frozen once the paper is published; the head of `v1` will be updated, minimally, to maintain compatibility with the HoTT library.  The main `master` branch will continue to evolve as we develop the library; as such, it is work in progress, and may contain loose ends and rough edges.

# Getting started #

To run/compile our files, you will need to download the HoTT library and a compatible version of Coq. To obtain these, follow the directions in the README and INSTALL files at [the HoTT/HoTT github repository](https://github.com/HoTT/HoTT).

Once you have these, assuming `hoqc` is in your system path, typing the command

    make

in the directory with these files will compile most files of the development.  You can then explore the files using Proof General or the Coq IDE.

If `hoqc` is not in your system path, you will need to pass its location explicitly:

    make COQC=/path/to/hoqc

By default, `make` omits the files `Pullbacks3.v` (slow to compile) and `Pullbacks3_alt.v` (extremely slow).  To include these, run `make all`.

# Organization #

The files in the library are as follows:

- Auxiliary.v: general-purpose lemmas, not morally part of our development but required by it.
- Fundamentals.v: fundamental constructions of the fibration category structure on types.
- Limits-common.v, Equalizers.v: core constructions used in the (otherwise independent) Pullbacks and Limits files.
- Pullbacks.v, Pullbacks2.v, Pullbacks3.v: the basic theory of (homotopy) pullbacks.
- Pullbacks3_alt.v: alternative approaches to the abstract two pullbacks lemma.
- Limits.v, Limits2.v: the basic theory of limits over graphs, with examples.
- Arith.v: a very bare-bones development of the natural numbers.
- PointedTypes.v: basic definitions regarding pointed types.
- LongExactSequences.v: the long exact sequence of a fibration, deduced from results on pullbacks.

# Versions and compatibility #

We aim to keep this development compatible with the latest version of the HoTT library.  Most recently, our revision c95e721 has been tested using HoTT revision 3500510:

  https://github.com/HoTT/HoTT/commit/3500510

To check out a specific version of this or the HoTT repo, run

    git checkout 1234abc

from within your local clone of the repository, where `1234abc` is the (abridged) hash of the desired commit, or the name of the desired branch.

This development may evolve in the future. The latest version can always be found at:

  https://github.com/peterlefanulumsdaine/hott-limits

The version submitted with the MSCS paper is archived, frozen, at:

  https://github.com/peterlefanulumsdaine/hott-limits/tree/MSCS

A branch based on that version, but minimally maintained for compatibility, is at:

  https://github.com/peterlefanulumsdaine/hott-limits/tree/v1
  
# Licensing #

The work contained in this directory is licensed under a Creative Commons Attribution 3.0 Unported License. For details, see: 

  http://creativecommons.org/licenses/by/3.0/deed.en_US
