
# Overview
This repository contains the artifact for the paper "Sound Inlining for Automatic Separation Logic Verifiers". It includes

- The soundness proof (Theorem 1) mechanized in Isabelle/HOL (./soundness)
- The completeness proof proved on paper (./completeness/completeness_proof.pdf)
- The examples used for the evaluation (./examples)
- A link to the source of the tool (https://github.com/tdardinier/carbon) and instructions how to install it

# Soundness Proof
The Isabelle/HOL formalization of the soundness theorem (Theorem 3.1) contains 3 files:
- ./soundness/SepAlgebra.thy: This theory formalizes the separation algebra of Definition 1.
- ./soundness/Semantics.thy: This theory formalizes the abstract verification language (Sect. 3.2) with its semantics, as well as mono and framing.
- ./soundness/Soundness.thy: This theory formalizes inlining (Definition 6), the soundness condition (Definition 9), and proves the soundness theorem (Theorem 3.1). The soundness theorem's name in the file is "soundness" and can be found at the very end.

The formalization works with both Isabelle 2019 and Isabelle 2020.

# Examples
The examples are split into subfolders. One for each verifier from which we took examples (these are the examples from Table 1) and one for the examples that mainly satisfy the syntactic condition (these are the examples from Table 2).

The names of the examples in Table 1 are slightly different to the names here (we shortened them in the paper due to space constraints). Here is the correspondence for those that are unclear:

* RelAcqRustARCStronger_inline represents rust_arc_1 and rust_arc_2. The client "new_clone" was inlined for rust_arc_2, while the remaining clients were inlined from rust_arc_1.
* RelAcqDblMsgPassSplit represents msg_pass_split_1 and msg_pass_split_2. The client "client_sound" was used for msg_pass_split_1 and the client "client_unsound" was used for msg_pass_split_2.
* vstte2012_problem2.vpr represents combinator


# Inlining Tool
The source for our inlining tool for Viper, which also checks the structural soundness condition is located at https://github.com/tdardinier/carbon 

## Installation

### Dependencies
- Z3 version 4.8.4: https://github.com/Z3Prover/z3/releases/tag/z3-4.8.4
- Boogie from this version: https://github.com/boogie-org/boogie/releases/tag/v2.4.21
- sbt: https://www.scala-sbt.org/
- Java JDK (at least version 8)

### Install main tool
1. Clone https://github.com/tdardinier/carbon [A] (this is the main tool)
2. Clone https://github.com/tdardinier/silver [B] (this is the Viper language). 
3. Create a symbolic link in the root of [A] to [B] with name "silver"
4. Compile the main tool by running "sbt compile" in the root of A

### Set dependencies
One can either provide explicit command-line options to the main tool for the 
Boogie and Z3 (shown below). Alternatively, one can set the path to the 
corresponding binaries  (boogie.exe and z3.exe) to environment variables 
BOOGIE_EXE (for Boogie) and  Z3_EXE (for Z3).

### Usage of tool
In the root of [A], execute "sbt run [options] [path_to_viper_file]".
The following command shows the most common options for a file test.vpr:

`sbt run --SI 2 --entry main --modularSC test.vpr`

- `--SI 2` sets the inlining bound to 2
- `--entry` main sets the main to the initial method to inline
- `--modularSC` is the option which performs an optimization that replaces
mono checks by framing checks and as a result can omit some framing checks 
(using that framing implies mono and the sequential composition of two framing 
statements is framing). This can lead to incompleteness, but is mostly not an 
issue in practice (we used it for all our examples in the evaluation).

If the BOOGIE_EXE and Z3_EXE environment variables were not set, then one can 
provide the paths to the corresponding binaries via explicit options. The above
command would then be:

`sbt run --SI 2 --entry main --modularSC --boogieExe [path to Boogie] --z3Exe [path to Z3] test.vpr`








