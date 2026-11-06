# Quintic SPR Proof

[简体中文](README.zh-CN.md)

A standalone Lean 4 / mathlib formalization of robust strictly positive-real (SPR) synthesis for real monic quintic interval polynomials.

## What this repository proves

For 5 independent finite closed coefficient intervals, including degenerate intervals, assume that **every denominator in the interval box is strictly Hurwitz** (all roots have negative real part). There exists **one fixed real numerator of exact degree 5** such that

$$
\operatorname{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0
\quad\text{for every denominator }a\text{ in the box and every }\omega\in\mathbb R.
$$

The same numerator works for the entire box and all real frequencies, including zero. This is an existence theorem, not a numerical synthesis algorithm or a theorem for arbitrary orders.

- Public theorem: [`SPR.N5.Direct.robustSPR`](Lean/Main.lean).
- Exact definitions: [`Lean/SPR/N5/Definitions/Frequency.lean`](Lean/SPR/N5/Definitions/Frequency.lean).
- [Module guide](Lean/SPR/N5/README.md) · [Proof outline](docs/PROOF.md) · [Verification notes](docs/VERIFICATION.md).

## Setup and build

Install Git and [elan](https://github.com/leanprover/elan), the Lean toolchain manager, and make sure `elan`, `lean`, and `lake` are on your PATH. The commands below work in a macOS, Linux, or Windows WSL shell and run from the repository root.

```sh
git clone https://github.com/dgjszy/quintic-spr-proof.git
cd quintic-spr-proof
lake exe cache get
lake build
```

`lean-toolchain` pins Lean **4.30.0**; mathlib is pinned to **v4.30.0**, with exact dependency commits in `lake-manifest.json`. The first run needs internet access to download the toolchain, dependencies, and compiled cache. Keep the lockfile; a normal build does not require `lake update`. The cache speeds up dependency builds; Lean checks the project proof sources.

This repository is used as a local proof library. No server or database deployment is needed. The formal build requires neither Python nor an external solver.

## Verify and use

```sh
lake env lean Lean/Audit.lean
```

The default build includes a transitive axiom audit that permits only `propext`, `Classical.choice`, and `Quot.sound`; any other axiom causes an error.

Within this project's Lean environment:

```lean
import SPR

#check SPR.N5.Direct.robustSPR
#print axioms SPR.N5.Direct.robustSPR
```

## Repository layout

- [`Lean/Main.lean`](Lean/Main.lean): public theorem and final proof assembly.
- [`Lean/SPR.lean`](Lean/SPR.lean): public import entry.
- [`Lean/SPR/N5/`](Lean/SPR/N5/): definitions and quintic proof modules.
- [`Lean/Audit.lean`](Lean/Audit.lean): axiom audit.
