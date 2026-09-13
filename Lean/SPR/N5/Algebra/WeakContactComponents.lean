import SPR.N5.Algebra.WeakCommonRoots

/-!
# WeakContactComponents

论文 §4.1–4.2：非负性的代数后果、分子零点及互素性。
在正接触处排除分子和分母分量为零；分母必须属于同一个区间族。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial

theorem denominatorEven_derivative_eval (a : Poly5) (t : ℝ) :
    (denominatorEvenPoly a).derivative.eval t = 2 * a.a1 * t - a.a3 := by
  simp [denominatorEvenPoly]
  ring

theorem denominatorOdd_derivative_eval (a : Poly5) (t : ℝ) :
    (denominatorOddPoly a).derivative.eval t = 2 * t - a.a2 := by
  simp only [denominatorOddPoly, derivative_add, derivative_sub, derivative_pow,
    derivative_X, derivative_mul, derivative_C, eval_add, eval_sub, eval_mul,
    eval_pow, eval_natCast, eval_X, eval_C, eval_one, eval_zero]
  ring

theorem Box5.positive_contact_even_ne_zero (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) {r : ℝ} (hr : 0 < r)
    (hc : generalPairing a b r = 0) : numeratorEven b r ≠ 0 := by
  intro he
  have ho : numeratorOdd b r ≠ 0 := fun ho =>
    K.no_common_positive_numerator_root hK hwidth hb hw hr he ho
  have hoa : oddPart a r = 0 := by
    simp only [generalPairing, he, zero_mul, zero_add] at hc
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left (ne_of_gt hr))).resolve_left ho
  have hd (v : ℝ) (hl : K.lower.a5 ≤ v) (hu : v ≤ K.upper.a5) :
      (pairingPoly {a with a5 := v} b).derivative.eval r = 0 := by
    apply nonnegative_contact_derivative hr
      (by simpa only [pairingPoly_eval] using hw _ (K.update_a5_mem ha hl hu))
    simpa [pairingPoly_eval, generalPairing, he, oddPart] using
      (show r * (numeratorOdd b r * oddPart a r) = 0 by rw [hoa]; ring)
  have heq := pairing_derivative_a5_difference a b r K.upper.a5 K.lower.a5
  rw [hd _ K.h5 le_rfl, hd _ le_rfl K.h5, sub_self] at heq
  have he' := (mul_eq_zero.mp heq.symm).resolve_left
    (ne_of_gt (sub_pos.mpr hwidth.2.2.2.2))
  have hbase : (pairingPoly a b).derivative.eval r = 0 :=
    nonnegative_contact_derivative hr
      (by simpa only [pairingPoly_eval] using hw a ha)
      (by simpa only [pairingPoly_eval] using hc)
  rw [pairing_derivative_eval, he, he', hoa] at hbase
  simp only [zero_mul, mul_zero, zero_add, add_zero] at hbase
  have hs := (mul_eq_zero.mp ((mul_eq_zero.mp hbase).resolve_left (ne_of_gt hr))).resolve_left ho
  obtain ⟨D⟩ := denominator_interlacing (hK a ha)
  exact D.odd_derivative_ne_zero hoa (by simpa only [denominatorOdd_derivative_eval] using hs)

theorem Box5.positive_contact_odd_ne_zero (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) {r : ℝ} (hr : 0 < r)
    (hc : generalPairing a b r = 0) : numeratorOdd b r ≠ 0 := by
  intro ho
  have he := K.positive_contact_even_ne_zero hK hwidth hb hw ha hr hc
  have hea : evenPart a r = 0 := by
    simp only [generalPairing, ho, zero_mul, mul_zero, add_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left he
  have hd (v : ℝ) (hl : K.lower.a4 ≤ v) (hu : v ≤ K.upper.a4) :
      (pairingPoly {a with a4 := v} b).derivative.eval r = 0 := by
    apply nonnegative_contact_derivative hr
      (by simpa only [pairingPoly_eval] using hw _ (K.update_a4_mem ha hl hu))
    simpa [pairingPoly_eval, generalPairing, ho, evenPart] using
      (show numeratorEven b r * evenPart a r = 0 by rw [hea]; ring)
  have hoq := pairing_derivative_a4_difference a b r K.upper.a4 K.lower.a4
  rw [hd _ K.h4 le_rfl, hd _ le_rfl K.h4, sub_self, ho, zero_add] at hoq
  have hot := (mul_eq_zero.mp hoq.symm).resolve_left
    (ne_of_gt (sub_pos.mpr hwidth.2.2.2.1))
  have ho' := (mul_eq_zero.mp hot).resolve_left (ne_of_gt hr)
  have hbase : (pairingPoly a b).derivative.eval r = 0 :=
    nonnegative_contact_derivative hr
      (by simpa only [pairingPoly_eval] using hw a ha)
      (by simpa only [pairingPoly_eval] using hc)
  rw [pairing_derivative_eval, ho, ho', hea] at hbase
  simp only [zero_mul, mul_zero, zero_add, add_zero] at hbase
  have hs := (mul_eq_zero.mp hbase).resolve_left he
  obtain ⟨D⟩ := denominator_interlacing (hK a ha)
  exact D.even_derivative_ne_zero (ne_of_gt (quintic_coefficients_pos (hK a ha)).1) hea
    (by simpa only [denominatorEven_derivative_eval] using hs)

theorem Box5.positive_contact_denominator_components_ne_zero (K : Box5)
    (hK : K.RobustlyHurwitz) (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) {r : ℝ} (hr : 0 < r)
    (hc : generalPairing a b r = 0) : evenPart a r ≠ 0 ∧ oddPart a r ≠ 0 := by
  have he := K.positive_contact_even_ne_zero hK hwidth hb hw ha hr hc
  have ho := K.positive_contact_odd_ne_zero hK hwidth hb hw ha hr hc
  have hnotboth : ¬ (evenPart a r = 0 ∧ oddPart a r = 0) := by
    rintro ⟨hea, hoa⟩
    have hz := hurwitz_frequencyValue_ne_zero (hK a ha) (Real.sqrt r)
    apply hz
    rw [frequencyValue_eq, Real.sq_sqrt hr.le, hea, hoa]
    simp
  constructor
  · intro hea
    have hoa : oddPart a r = 0 := by
      simp only [generalPairing, hea, mul_zero, zero_add] at hc
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left (ne_of_gt hr))).resolve_left ho
    exact hnotboth ⟨hea, hoa⟩
  · intro hoa
    have hea : evenPart a r = 0 := by
      simp only [generalPairing, hoa, mul_zero, add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left he
    exact hnotboth ⟨hea, hoa⟩

end
end SPR.N5.Direct
