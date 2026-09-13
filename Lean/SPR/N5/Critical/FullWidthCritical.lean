import SPR.N5.Critical.StableExpansion

/-!
# FullWidthCritical

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
从原命题的反例得到非退化临界族；较强的结构化版本另调用 §4 的分子结论。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial

/-- An obstruction to the original (possibly degenerate) box produces a
full-width stable box carrying a nonzero weak numerator and a moment certificate.
The auxiliary box need not be a subset of the original box. -/
theorem Box5.fullWidth_critical_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ L : Box5, L.RobustlyHurwitz ∧ L.FullWidth ∧
      ∃ b : Vec6, ‖b‖ = 1 ∧ b ≠ 0 ∧ 0 ≤ b 0 ∧
        (∀ a : Poly5, L.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ∧
        Nonempty (MomentCertificate L b) := by
  obtain ⟨ε,hε,hs,hw⟩ := K.exists_stable_fullWidth_expansion hK
  let J := K.expand ε hε.le
  have hjno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, J.Contains a → FrequencySPR a.toPoly b := by
    rintro ⟨b,hb,hf⟩
    exact hno ⟨b,hb,fun a ha => hf a (K.expand_subset hε.le ha)⟩
  obtain ⟨θ,hθ,hθ1,hL,b,hbn,hbp,hb0,hweak,hcert⟩ := J.critical_moment_certificate hs hjno
  exact ⟨J.contract θ hθ.le, hL, J.contract_fullWidth hw hθ, b, hbn,
    (by intro he; simp [he] at hbn), hb0, hweak, hcert⟩

/-- The weak numerator in a putative counterexample has certified coprime
parts and the precise quartic or quintic interlacing structure. -/
theorem Box5.structured_critical_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ L : Box5, L.RobustlyHurwitz ∧ L.FullWidth ∧
      ∃ b : Vec6, b ≠ 0 ∧ 0 ≤ b 0 ∧
        (0 < b 1 ∧ 0 < b 2 ∧ 0 < b 3 ∧ 0 < b 4 ∧ 0 ≤ b 5) ∧
        (∀ a : Poly5, L.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ∧
        IsCoprime (numeratorEvenPoly b) (numeratorOddPoly b) ∧
        ((b 0 = 0 ∧ Nonempty (QuarticNumeratorInterlacing b)) ∨
          (0 < b 0 ∧ Nonempty (QuinticNumeratorInterlacing b))) ∧
        Nonempty (MomentCertificate L b) := by
  obtain ⟨L,hL,hwidth,b,hbn,hb,hb0,hw,hcert⟩ := K.fullWidth_critical_certificate hK hno
  refine ⟨L,hL,hwidth,b,hb,hb0,L.weak_numerator_coefficients hL hwidth hb hb0 hw,
    hw,L.weak_numerator_isCoprime hL hwidth hb hb0 hw,?_,hcert⟩
  rcases eq_or_lt_of_le hb0 with hz | hp
  · exact Or.inl ⟨hz.symm,L.weak_quartic_interlacing hL hwidth hb hz.symm hw⟩
  · exact Or.inr ⟨hp,L.weak_quintic_interlacing hL hwidth hb hp hw⟩

end
end SPR.N5.Direct
