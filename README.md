# Quintic SPR Proof

A Lean 4 / mathlib proof of robust strictly positive-real synthesis for real monic quintic interval polynomials.

五阶区间多项式族鲁棒严格正实综合的完整 Lean 形式化证明。

## The theorem

Let

$$K=\{s^5+a_1s^4+a_2s^3+a_3s^2+a_4s+a_5:\ a_k\in[l_k,u_k]\},$$

where the endpoints are finite real numbers and $l_k\le u_k$; degenerate intervals are allowed.
If every polynomial in $K$ is strictly Hurwitz, there exists **one fixed real polynomial $b$ of exact degree five** such that

$$\operatorname{Re}\!\left(\frac{b(i\omega)}{a(i\omega)}\right)>0
\qquad\text{for every }a\in K\text{ and every }\omega\in\mathbb R.$$

The numerator may depend on the interval endpoints, but is independent of the denominator and frequency.
The theorem is an existence proof, not a numerical synthesis algorithm.

- Formal statement: [`RobustSPRStatement`](Lean/SPR/N5/Definitions/Frequency.lean).
- Main theorem: [`SPR.N5.Direct.robustSPR`](Lean/Main.lean).
- Proof guide: [module map](Lean/SPR/N5/README.md) and [proof outline](docs/PROOF.md).
- Trust boundary and build checks: [verification](docs/VERIFICATION.md).

## Build

Install Lean's `elan` toolchain manager, then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean Lean/Audit.lean
```

`lean-toolchain` pins Lean **4.30.0**. Mathlib is pinned to **v4.30.0** and its exact dependency commits are recorded in `lake-manifest.json`.
The cache command downloads compiled dependencies; the project proof sources are checked by Lean.
No Python, external solver, or generated proof source is required.

To use the theorem:

```lean
import SPR

#check SPR.N5.Direct.robustSPR
#print axioms SPR.N5.Direct.robustSPR
```

The default build includes a transitive axiom audit of every theorem in the `SPR` namespace.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

## Contents

- `Lean/Main.lean`: the actual public theorem and final proof assembly.
- `Lean/SPR.lean`: public import entry.
- `Lean/Audit.lean`: build-time axiom audit.
- `Lean/SPR/N5/`: definitions and the complete quintic proof.
- `docs/`: proof and verification notes.

This standalone repository contains the quintic proof only. It makes no claim about a general higher-order theorem.
