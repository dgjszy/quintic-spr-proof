import SPR.N5.Algebra.WeakInterlacing

/-!
# WeakCoprime

论文 §4.1–4.2：非负性的代数后果、分子零点及互素性。
从已证的根序与零点排除得到分子偶奇部分互素。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial

theorem linear_isCoprime_of_eval_ne_zero {p : ℝ[X]} {r : ℝ} (hr : p.eval r ≠ 0) :
    IsCoprime (X - C r) p := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).mpr
  intro z
  by_cases he : z = (r : ℂ)
  · right
    subst z
    change p.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) r) ≠ 0
    rw [eval₂_at_apply]
    simpa using
      (show ((p.eval r : ℝ) : ℂ) ≠ 0 by exact_mod_cast hr)
  · left
    simpa [sub_ne_zero] using he

theorem Box5.weak_numerator_isCoprime (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    IsCoprime (numeratorEvenPoly b) (numeratorOddPoly b) := by
  obtain ⟨D⟩ := denominator_interlacing (hK K.lower K.lower_mem)
  obtain ⟨e,f,he0,heo,hof,hfo,hEf⟩ := K.weak_even_root_locations hK hwidth hb hw K.lower_mem D
  have hE (t : ℝ) : numeratorEven b t = b 1 * ((t-e)*(t-f)) := by
    have h := congrArg (fun p : ℝ[X] => p.eval t) hEf
    simpa only [numeratorEvenPoly_eval, eval_mul, eval_sub, eval_C, eval_X] using h
  obtain ⟨hOe,hOf⟩ := K.odd_signs_at_even_roots hK hwidth hb hb0 hw K.lower_mem D
    he0 heo hof hfo (by simp [hE]) (by simp [hE])
  have hcop : IsCoprime ((X - C e) * (X - C f)) (numeratorOddPoly b) :=
    (linear_isCoprime_of_eval_ne_zero (by simpa only [numeratorOddPoly_eval] using ne_of_gt hOe)).mul_left
      (linear_isCoprime_of_eval_ne_zero (by simpa only [numeratorOddPoly_eval] using ne_of_lt hOf))
  have hb1 := (K.weak_numerator_coefficients hK hwidth hb hb0 hw).1
  have hc : IsUnit (C (b 1) : ℝ[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hb1))
  rw [hEf, isCoprime_mul_unit_left_left hc]
  exact hcop

theorem QuinticNumeratorInterlacing.origin_iff {b : Vec6} (D : QuinticNumeratorInterlacing b)
    (hb1 : 0 < b 1) : b 5 = 0 ↔ D.e = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval 0) D.even_factor
  have hf : 0 < D.f := (lt_of_le_of_lt D.e_nonneg D.e_lt_k).trans D.k_lt_f
  have hc : b 5 = b 1 * (D.e * D.f) := by simpa [numeratorEvenPoly] using h
  rw [hc]
  simp [ne_of_gt hb1, ne_of_gt hf, mul_eq_zero]

theorem QuarticNumeratorInterlacing.origin_iff {b : Vec6} (D : QuarticNumeratorInterlacing b)
    (hb1 : 0 < b 1) : b 5 = 0 ↔ D.e = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval 0) D.even_factor
  have hf : 0 < D.f := (lt_of_le_of_lt D.e_nonneg D.e_lt_k).trans D.k_lt_f
  have hc : b 5 = b 1 * (D.e * D.f) := by simpa [numeratorEvenPoly] using h
  rw [hc]
  simp [ne_of_gt hb1, ne_of_gt hf, mul_eq_zero]

end
end SPR.N5.Direct
