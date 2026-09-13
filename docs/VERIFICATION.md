# Verification and trust boundary

The public theorem is `SPR.N5.Direct.robustSPR`; its exact proposition is
`SPR.N5.Direct.RobustSPRStatement`. Definitions explicitly retain independent closed
coefficient intervals, equality of endpoints, strict Hurwitz stability of every
member, one fixed numerator of exact degree five, and every real frequency.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Lean/Audit.lean
```

The pinned environment is Lean 4.30.0 and mathlib v4.30.0, at commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. The complete dependency lock is
`lake-manifest.json`.

`Audit` is a default build root. It collects the transitive axioms of every theorem
whose name begins with `SPR` and fails if any axiom other than `propext`,
`Classical.choice`, or `Quot.sound` occurs. It also prints the public theorem's type
and its axioms. These are kernel checks; no Python program, numerical certificate,
external solver or runtime-generated proof source is required.

## Standalone extraction

All 65 included Lean source files are byte-for-byte identical to the quintic proof
in the source project's commit `d95c56d77a108486db9020648847ca383fa918fc`.
The extraction keeps all 62 `SPR.N5` modules and the three public/build entry files.
The unused research compatibility import is omitted. Documentation and the root
Lake package name are adjusted for this standalone repository; dependency commits
are unchanged.

The repository starts with a fresh history containing only the quintic proof,
its build configuration and these notes.

## Standalone validation — 2026-09-13

- Built the exported repository with an initially empty project output directory.
  The pinned third-party dependency cache was reused in an isolated copy; no old
  project proof outputs were copied. `lake build` passed (8540 jobs including
  dependencies).
- The default audit checked 892 theorems, including generated auxiliaries. The
  public theorem and every audited theorem use only the three allowed axioms.
- A separate Lean check expanded the statement into the entire coefficient box,
  strict negativity of every denominator root's real part, one exact-degree-five
  numerator, and every real frequency. It type-checked directly against the
  published theorem.
- A temporary negative test injected an additional axiom into the audit's
  namespace. The unchanged audit rejected it as expected. The test was not
  included in this repository.
- Every included Lean file was compared byte-for-byte with the source commit.
  All local imports resolve inside this repository or the pinned dependencies.
- Existing style/linter warnings are retained; they do not indicate a failed
  theorem or an additional axiom.
