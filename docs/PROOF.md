# Proof outline

The exact theorem is stated in `SPR.N5.Direct.RobustSPRStatement` and proved by
`SPR.N5.Direct.robustSPR`. All steps below are part of the Lean import chain.

1. **Definitions and frequency algebra.** Represent a monic quintic coefficient box, strict Hurwitz stability, and the all-family/all-real-frequency condition. Convert the real-part condition into polynomial pairings and prove the relevant corner reduction.
2. **Root geometry.** Establish denominator interlacing, common root bands, and the coefficient/phase signs used later.
3. **Critical certificate.** Starting from a hypothetical failure on the original box, construct full-width critical data and a finite moment certificate. Stable expansion handles degenerate original intervals; boundary frequencies and infinity are retained where required.
4. **Algebra and interpolation.** Extract root, coprimality, and degree constraints from the nonnegative pairings and vanishing moments. Merge repeated frequency nodes without losing the certificate.
5. **Contacts and complete classification.** Convert actual contacts to ordered candidates, prove the enumeration complete, and reduce the surviving configurations to the terminal cases.
6. **Comparison and exclusion.** Root-ratio inequalities exclude the terminal configurations, including the zero-constant and lower-degree boundary cases.
7. **Assembly.** `CertificateExclusion` rules out the critical certificate; `Main` concludes existence of an exact-degree-five numerator for the original box.

The [detailed module map](../Lean/SPR/N5/README.md) gives names and source links for each part.
The proof is nonconstructive. The exported statement requires strict positivity at every finite real frequency; it does not substitute a lower-degree numerator or restrict the family to a sampled set.
