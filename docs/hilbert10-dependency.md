# Dependencies and verification

The project uses:

- Lean `v4.35.0` (stable).
- [Mathlib](https://github.com/leanprover-community/mathlib4), revision
  `56a005855ea17e0b0958f73ec801ae140b0a1679` (release `v4.35.0`).
- Cameron Freer's [Hilbert 10 library](https://github.com/cameronfreer/hilbert10),
  revision `53313aa90c6b75c43eb3b16b64ad32fce33042cf`, licensed under
  [Apache-2.0](https://github.com/cameronfreer/hilbert10/blob/53313aa90c6b75c43eb3b16b64ad32fce33042cf/LICENSE).

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` fix the toolchain
and dependencies. Keep the manifest when distributing the project.

## Build

With Elan and Git installed, run from the project root:

```sh
lake exe cache get
lake build
```

The first command obtains the precompiled Mathlib cache. The second builds
the reduction, the main matrix statements, the control-class equivalences,
and the axiom checks. No separate Hilbert 10 installation or source patch
is required.

The Hilbert 10 revision originally specifies Lean `v4.35.0-rc4` and an older
Mathlib revision. This project's root configuration selects Lean `v4.35.0`
and the stable Mathlib revision above, with its transitive dependencies.
The Hilbert 10 source is unchanged. Its experimental library is not part
of the theorem import chain or the default build of this project.

## Hilbert 10 theorem

The undecidability proofs import `Hilbert10.not_computablePred_intSolvable`
from `Hilbert10.Endpoints`. The bridge in `scripts/VerifyUndecidability.lean`
proves that its integer-polynomial evaluator agrees with the polynomial
representation used by the control reduction.

`scripts/CheckStatements.lean` checks axiom dependencies of the control
library. `scripts/VerifyUndecidability.lean` checks the undecidability
results. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The matrix statements and control-class equivalences also
print their axiom dependencies during compilation.
