/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Fast.Cli
public import Ratpoints.Fast.Mask
public import Ratpoints.Fast.Search
public import Ratpoints.Fast.Sieve

/-!
# The fast search

A search for the points that is not a model of the C code, built for speed in Lean, and the
program `ratpoints-lean` on it. It is plain executable code on Lean core and `Std` and the brute
force of the model, except for the two primitives of `Ratpoints.Mask`, whose C code
(`@[extern c inline]`) works on 64-bit words; their Lean bodies are the reference definitions
that the proofs use (`scripts/check_layout.py` allows `extern` only there).

* `Ratpoints.Fast.fastPoints` (`Ratpoints.Fast.Sieve`): the sieve with the bit masks held in
  natural numbers;
* `Ratpoints.FastMask.fastPoints` (`Ratpoints.Fast.Search`): the same sieve with the bit masks
  held in byte arrays (`Ratpoints.Fast.Mask`), the search of the program;
* `Ratpoints.FastCli.main` (`Ratpoints.Fast.Cli`): the program.
-/
