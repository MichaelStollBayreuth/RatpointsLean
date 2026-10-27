---
layout: default
title: RatpointsLean
---

<header class="page-header">
  <h1>{{ site.title }}</h1>
</header>

[`ratpoints`](https://github.com/MichaelStollBayreuth/ratpoints) is a C program by
[Michael Stoll](https://www.mathe2.uni-bayreuth.de/stoll/) that finds the rational points of
bounded height on the curves `y² = F(x, z)`, where `F` is a binary form of even degree with integer
coefficients, by sieving. This project builds a model of it in [Lean 4](https://lean-lang.org)
that mirrors the hardware-independent structure of the C code function by function, proves with
[Mathlib](https://github.com/leanprover-community/mathlib4) that the model meets a short
specification for every choice of the sieving parameters, and links the model to the C code by a
record of which Lean definition models which lines of C, checked in CI, and by differential tests.

- [Blueprint]({{ site.baseurl }}/blueprint/): the specification, the components of the model with
  their contracts, and the correspondence with the C code
  ([PDF version]({{ site.baseurl }}/blueprint.pdf))
- [API documentation]({{ site.baseurl }}/docs/), generated from the Lean sources
- [Source code](https://github.com/MichaelStollBayreuth/RatpointsLean) on GitHub
