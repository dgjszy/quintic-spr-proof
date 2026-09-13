import SPR.N5.Algebra.WeakNumeratorCoefficients

/-!
# WeakRootLocations

论文 §4.1–4.2：非负性的代数后果、分子零点及互素性。
用实二次式的符号给出分子根的位置，分别保留四次与五次情形。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial Filter Set
open scoped Topology

theorem root_between_strict_signs {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ}
    (hxy : x < y) (hx : f x < 0) (hy : 0 < f y) :
    ∃ r : ℝ, x < r ∧ r < y ∧ f r = 0 := by
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hxy.le hf.continuousOn ⟨hx.le, hy.le⟩
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_, hfr⟩
  · intro he
    rw [← he] at hfr
    linarith
  · intro he
    rw [he] at hfr
    linarith

theorem root_between_reverse_signs {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ}
    (hxy : x < y) (hx : 0 < f x) (hy : f y < 0) :
    ∃ r : ℝ, x < r ∧ r < y ∧ f r = 0 := by
  obtain ⟨r, hrx, hry, hr⟩ := root_between_strict_signs hf.neg hxy (neg_neg_of_pos hx) (neg_pos.mpr hy)
  exact ⟨r, hrx, hry, neg_eq_zero.mp hr⟩

theorem root_nonneg_before {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : 0 < x) (h0 : 0 ≤ f 0) (hfx : f x < 0) :
    ∃ r : ℝ, 0 ≤ r ∧ r < x ∧ f r = 0 := by
  by_cases hzero : f 0 = 0
  · exact ⟨0, le_rfl, hx, hzero⟩
  · obtain ⟨r, hr0, hrx, hfr⟩ := root_between_reverse_signs hf hx
      (lt_of_le_of_ne h0 (Ne.symm hzero)) hfx
    exact ⟨r, hr0.le, hrx, hfr⟩

theorem numeratorEvenPoly_eval (b : Vec6) (t : ℝ) :
    (numeratorEvenPoly b).eval t = numeratorEven b t := by
  simp [numeratorEvenPoly, numeratorEven]

theorem numeratorOddPoly_eval (b : Vec6) (t : ℝ) :
    (numeratorOddPoly b).eval t = numeratorOdd b t := by
  simp [numeratorOddPoly, numeratorOdd]

theorem Box5.weak_even_root_locations (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) (D : DenominatorInterlacing a) :
    ∃ e f : ℝ, 0 ≤ e ∧ e < D.o₁ ∧ D.o₁ < f ∧ f < D.o₂ ∧
      numeratorEvenPoly b = C (b 1) * ((X - C e) * (X - C f)) := by
  obtain ⟨_,_,hE1,hE2⟩ := K.weak_signs_at_interlacing hK hwidth hb hw ha D
  have hb5 := weak_numerator_constant_nonneg (hK a ha) (hw a ha)
  have hcont : Continuous (numeratorEven b) := by unfold numeratorEven; fun_prop
  have ho1 := D.e₁_pos.trans D.e₁_lt_o₁
  have ho12 := D.o₁_lt_e₂.trans D.e₂_lt_o₂
  obtain ⟨e, he0, heo, he⟩ := root_nonneg_before hcont ho1
    (by simpa [numeratorEven] using hb5) hE1
  obtain ⟨f, hof, hfo, hf⟩ := root_between_strict_signs hcont ho12 hE1 hE2
  have hdeg : (numeratorEvenPoly b).natDegree ≤ 2 := by
    unfold numeratorEvenPoly
    compute_degree!
  have hform := quadratic_factor_of_two_roots hdeg (ne_of_lt (heo.trans hof))
    (by simpa only [numeratorEvenPoly_eval] using he)
    (by simpa only [numeratorEvenPoly_eval] using hf)
  refine ⟨e, f, he0, heo, hof, hfo, ?_⟩
  simpa [numeratorEvenPoly, coeff_add, coeff_sub, coeff_C_mul_X_pow] using hform

theorem Box5.weak_quintic_odd_root_locations (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 < b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) (D : DenominatorInterlacing a) :
    ∃ k l : ℝ, D.e₁ < k ∧ k < D.e₂ ∧ D.e₂ < l ∧
      numeratorOddPoly b = C (b 0) * ((X - C k) * (X - C l)) := by
  obtain ⟨hO1,hO2,_,_⟩ := K.weak_signs_at_interlacing hK hwidth hb hw ha D
  have hcont : Continuous (numeratorOdd b) := by unfold numeratorOdd; fun_prop
  have he12 := D.e₁_lt_o₁.trans D.o₁_lt_e₂
  obtain ⟨k, hek, hke, hk⟩ := root_between_reverse_signs hcont he12 hO1 hO2
  have hdeg : (numeratorOddPoly b).natDegree = 2 := by
    have hb0ne := ne_of_gt hb0
    unfold numeratorOddPoly
    compute_degree!
  have hlc : (numeratorOddPoly b).leadingCoeff = b 0 := by
    rw [← coeff_natDegree, hdeg]
    simp [numeratorOddPoly, coeff_add, coeff_sub, coeff_C_mul_X_pow]
  have htendsto := (numeratorOddPoly b).tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.mp (by rw [hdeg]; omega)) (by rw [hlc]; exact hb0.le)
  have hpos : ∀ᶠ t in atTop, 0 < numeratorOdd b t := by
    simpa only [numeratorOddPoly_eval] using htendsto.eventually_gt_atTop 0
  obtain ⟨v, hev, hv⟩ := ((eventually_gt_atTop D.e₂).and hpos).exists
  obtain ⟨l, hel, hlv, hl⟩ := root_between_strict_signs hcont hev hO2 hv
  have hform := quadratic_factor_of_two_roots hdeg.le (ne_of_lt (hke.trans hel))
    (by simpa only [numeratorOddPoly_eval] using hk)
    (by simpa only [numeratorOddPoly_eval] using hl)
  refine ⟨k, l, hek, hke, hel, ?_⟩
  simpa [numeratorOddPoly, coeff_add, coeff_sub, coeff_C_mul_X_pow] using hform

theorem Box5.weak_quartic_odd_root_location (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : b 0 = 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) (D : DenominatorInterlacing a) :
    ∃ k : ℝ, D.e₁ < k ∧ k < D.e₂ ∧
      numeratorOddPoly b = C (-(b 2)) * (X - C k) := by
  obtain ⟨hO1,hO2,_,_⟩ := K.weak_signs_at_interlacing hK hwidth hb hw ha D
  have hb2 := (K.weak_numerator_coefficients hK hwidth hb (by rw [hb0]) hw).2.1
  refine ⟨b 4 / b 2, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hb2).mpr
    simp only [numeratorOdd, hb0, zero_mul, zero_sub] at hO1
    nlinarith
  · apply (div_lt_iff₀ hb2).mpr
    simp only [numeratorOdd, hb0, zero_mul, zero_sub] at hO2
    nlinarith
  · have hmul : b 2 * (b 4 / b 2) = b 4 := mul_div_cancel₀ _ (ne_of_gt hb2)
    simp only [numeratorOddPoly, hb0, map_zero, zero_mul, zero_sub, map_neg,
      mul_sub, neg_mul, ← map_mul, hmul]
    ring

end
end SPR.N5.Direct
