# Reusable toolkit for safe collision avoidance maneuver computation during aircraft encounters

## What is this?

This repository contains two peer-reviewed publications describing the
development of mathematics and software tools for making safe
collision avoidance decisions in the horizontal axes for
simultaneously turning vehicles. It includes a reusable library, and
formal, machine checked proofs of the correctness of the mathematics
in that library for turning kinematics.

## Documentation

The first paper titled

*"Formally Verified Timing Computation for Non-deterministic Horizontal
Turns During Aircraft Collision Avoidance Maneuvers"*

was presented at the conference on Formal Methods for Industrial
Critical Systems in 2020. The paper develops a library of lemmas and
applies the library to creating timing guarantees for collision
avoidance during horizontal turns.

Abstract:

We develop a library of proofs to support rigorous mathematical
reasoning about horizontal aircraft turning maneuvers, and apply it to
formally verify a timing computation for use during mixed horizon- tal
and vertical aircraft collision avoidance maneuvers. We consider turns
that follow non-deterministic circular turn-to-bearing horizontal
motion, formalizing path-length and timing properties. These
kinematics are the building blocks for Dubins trajectories, and can be
used to formalize a variety of techniques, including those that
contain non-determinism. The timing computation establishes, for
intersecting trajectories, the exact bounds of time intervals when the
horizontal position of the aircraft might coincide, and during which
they must be at diﬀerent altitudes to avoid collision.

The second paper titled

*"Envelopes and waves: safe multivehicle collision avoidance for
horizontal non-deterministic turns"*

is an invited paper, an extended version of the above published in the
International Journal on Software Tools for Technology Transfer in
2022. It presents the application of the library to develop formally
verified timing computations, proposes a computationally efficient
approach to making safe, correct decisions for collision avoidance,
and discusses how these techniques can be combined with vertical
guarantees developed elsewhere to ensure safe collision avoidance for
aircraft encounters.

Abstract:

We present an approach to analyze the safety of asynchronous,
independent, non-deterministic, turn-to-bearing horizontal maneuvers
for two vehicles. Future turn rates, final bearings, and continuously
varying ground speeds throughout the encounter are unknown but
restricted to known ranges. We develop a library of formal proofs
about turning kinematics and apply the library to create a formally
verified timing computation. Additionally, we create a technique that
evaluates future collision possibilities that is based on waves of
position possibilities and relies on the timing computation. The
result either determines that the encounter will be collision-free, or
computes a safe overapproximation for when and where collisions may
occur.

Main lemmas provided as html in doc/ folder for users who don't
want to install Coq and don't need to machine-check proofs
themselves.

## Dependencies

These proofs formalizing horizontal one-turn-to-bearing motion were
developed with the Coq proof assistant v. 8.12.0 and the Coquelicot
real library v. 3.1.0.

One reliable way to get set up to check these proofs is to use the
opam package manager.

First use the package manager on your system to install opam, e.g.

```
$ sudo apt-get install opam
```

In some environments (e.g. if opam is already on your system)
it might be necessary to 

```
$ opam init

$ opam init env
```

Then you can install coq and coquelicot, letting opam handle
dependencies:

```
$ opam repo add coq-released https://coq.inria.fr/opam/released

$ opam install coq

$ opam install coq-coquelicot
```

## To build and check the proofs

```
$ coqtop --version
The Coq Proof Assistant, version 8.12.0 (October 2020)
compiled on Oct 3 2020 17:19:54 with OCaml 4.08.1

$ make
```

You can Print Assumptions to see axioms of the development.

## About me

Work/projects: https://www.linkedin.com/in/ykouskoulas

Publications:  https://orcid.org/0000-0001-7347-7473

This repo:     https://github.com/ykouskoulas/ottb-foundation-proofs
