# RatpointsLean

A Lean 4 model of [ratpoints](https://github.com/MichaelStollBayreuth/ratpoints), the C program
that finds the rational points of bounded height on the curves `y² = F(x, z)`, where `F` is a
binary form of even degree with integer coefficients, by sieving; with proofs that the model meets
a short specification for every choice of the sieving parameters, and a record, checked in CI, of
which Lean definition models which lines of C.

The C code is that of ratpoints 3.1.1; the project moves to each new release of ratpoints, and a
new optimization of the C code comes, as far as possible, with its soundness proof here.

**Status.** Stage A is done: the repository, the libraries, CI, the blueprint skeleton, the
correspondence record and its checks, the comparator harness, and the blueprint chapter that settles
the specification. Stage B is under way: the specification is in Lean, the brute-force reference
lists exactly its points, each once (certified by Comparator), and the command-line program
`ratpoints-lean` prints them; the differential tests against the C program come next. The blueprint
and the API documentation will be at <https://michaelstollbayreuth.github.io/RatpointsLean/> once
the repository is public.

## Layout

| part | contents | depends on |
|---|---|---|
| `Ratpoints/Model` | the executable model as plain code, one definition per component of the C code; no Mathlib, no contracts, no experimental options | Lean core, `Std` |
| `Ratpoints/Spec` | the specification: the binary form, the normalized points of height at most `H` | Mathlib |
| `Ratpoints/Proof` | the contract of each component as a theorem, and the main theorems | Mathlib, the specification, the model, the candidates for Mathlib |
| `Ratpoints/Mathlib` | statements of general interest, as candidates for Mathlib | Mathlib |
| `comparator/` | the specification restated, and the main theorems with `sorry`, for [Comparator](https://github.com/leanprover/comparator); their proofs by the library | Mathlib, the model (the challenge); the library (the solution) |
| `correspondence/` | the pin of the C code and the record of its correspondence with the model | — |
| `blueprint/` | the blueprint: specification, components with their contracts, links to the C code | — |

The model is a separate library, `RatpointsModel`, so that the executable and the differential
tests depend on it alone.

## Building and checking

```bash
lake exe cache get
lake build                                   # the model, the library and ratpoints-lean
lake exe ratpoints-lean '-2 0 0 1' 130       # the points of height at most 130 on y² = x³ - 2
python3 scripts/check_layout.py              # imports, the restrictions on the model, axioms
python3 scripts/correspondence.py check      # the correspondence with the C code at the pin
```

`scripts/correspondence.py` reads the C code from a clone of ratpoints that contains the pinned
commit, given by `--repo PATH` or the environment variable `RATPOINTS_REPO`. CI runs these checks
and more (`.github/workflows/build-project.yml`). `scripts/run-comparator.sh` runs Comparator
(`comparator/README.md`).

## The program `ratpoints-lean`

`ratpoints-lean 'a_0 a_1 ... a_n' H [options]` has the command line of ratpoints. It reads the
coefficients (constant term first), the height bound and the options as ratpoints does, with its
checks, messages and exit statuses, and prints the points of height at most `H` on
`y² = a_n xⁿ + ⋯ + a_0` as ratpoints does with `-q`: one line `(x : y : z)` per point. For now
it finds the points by brute force; it accepts `-q`, `-v` and the options that tune the sieve,
checking their arguments, but ignores them; it answers the other options of ratpoints with the
exit status 12; and it does not refuse a polynomial that is not squarefree.

## Licence

Apache 2.0 (`LICENSE`). The C code of ratpoints is under the GPL; its copyright notices name
Michael Stoll alone.
