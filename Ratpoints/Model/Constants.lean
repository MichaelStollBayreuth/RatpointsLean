/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The compile-time constants of ratpoints

The constants that the C code of ratpoints fixes when it is compiled, each a definition with the
value of the default build and a docstring that names its macro. Changing a definition changes the
model as changing the macro changes the C program: no proof depends on the values.

## Main definitions

* `Ratpoints.maxDegree`: the largest degree that ratpoints accepts.
-/

@[expose] public section

namespace Ratpoints

/-- The largest degree of a polynomial that ratpoints accepts, `RATPOINTS_MAX_DEGREE`: a list of
coefficients has at most `maxDegree + 1` entries.

C: `ratpoints.h:33` -/
def maxDegree : Nat := 100

end Ratpoints

end
