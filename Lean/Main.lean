import SPR.N5.Synthesis.CertificateExclusion

/-!
# Fifth-order interval robust SPR synthesis

Paper Theorem 1.1 and §7. Failure on an arbitrary stable box, including degenerate
intervals, gives the nondegenerate critical data of §3. The algebra, interpolation,
classification and ratio comparisons assembled in `CertificateExclusion` rule out
those data. `RobustSPRStatement` is defined in `SPR.N5.Definitions.Frequency`.

Read `Lean/SPR/N5/README.md` for the section-by-section correspondence.
Import `Main` directly, or use the public library entry `SPR`.
-/

namespace SPR.N5.Direct
noncomputable section

/-- Robust strictly positive-real synthesis for every real monic quintic interval
box, including degenerate intervals. The numerator has exact degree five, and
strict positivity holds at every real frequency for every denominator in the box. -/
theorem robustSPR : RobustSPRStatement := by
  intro K hK
  by_contra hno
  obtain ⟨L, hL, hwidth, b, _, hb, hb0, hnonneg, ⟨M⟩⟩ :=
    K.fullWidth_critical_certificate hK hno
  exact L.no_weak_moment_certificate hL hwidth hb hb0 hnonneg M

end
end SPR.N5.Direct
