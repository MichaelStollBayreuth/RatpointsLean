/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Comparator challenge statements

The main theorems of the project, stated with `sorry` for
[leanprover/comparator](https://github.com/leanprover/comparator), over a verbatim restatement of
the specification. The file may import only Mathlib and the model (`scripts/check_layout.py`
checks this): the main theorems speak about the model's `findPoints`, which is trusted in the
sense that it is the code the executable runs, while the specification is reproduced here, so
that a solution that changed it would be rejected.

The statements come in stage by stage, as `comparator/README.md` lists them: first the two
theorems of stage B (the brute-force reference finds exactly the points, without duplicates),
then the membership and no-duplicates theorems for `findPoints` together with the
well-formedness of the default parameters (stage C1), and the refusal theorem (stage D). Until
the first of them the file holds no theorem and no import.
-/
