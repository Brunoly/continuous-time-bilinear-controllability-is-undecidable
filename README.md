# Controllability of continuous-time bilinear systems is undecidable

There is no general algorithm that can decide whether a given continuous-time bilinear system is globally controllable. The problem is undecidable.

This repository contains a proof and a formalization in Lean.

## Problem definition

Consider the continuous-time bilinear system

```math
\dot x(t)=\left(A+\sum_{i=1}^{m}u_i(t)B_i\right)x(t),
\qquad x(t)\in\mathbb R^n.
```

The system is globally controllable if every nonzero initial state can be steered exactly to every nonzero target state in finite time using unrestricted controls.

We prove the impossibility of a general algorithm capable of determining, given rational matrices $A,B_1,\ldots,B_m$, whether the system is globally controllable.

This [manuscript](docs/continuous-bilinear-undecidability.md) contains the natural-language proof.

[MainTheorems.lean](MainTheorems.lean) contains the two main undecidability statements and the definitions they use, down to Mathlib.
[ControlClassTheorems.lean](ControlClassTheorems.lean) shows that the theorems hold for both piecewise-constant and $`L^1_{\mathrm{loc}}`$ controls.
The proof modules are in [ContinuousBilinear/](ContinuousBilinear/).

The formalization uses Lean 4.35.0, Mathlib, and Cameron Freer’s [formalization of Hilbert’s tenth problem](https://github.com/cameronfreer/hilbert10).

```sh
lake exe cache get
lake build
```

See [Dependencies and verification](docs/hilbert10-dependency.md) for the exact versions and verification details.

AI use: We used GPT-6 Astra Pro to find the proofs and formalized the results in Lean using Astra and GPT Sol.

Bruno Yamamoto. Code: [Apache-2.0](LICENSE).