import SPR.N5.Algebra.WeakRootLocations

/-!
# WeakInterlacing

论文 §4.1–4.2：非负性的代数后果、分子零点及互素性。
整理为四次和五次分子的严格交错结构，允许偶部第一个根位于原点。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial

theorem Box5.odd_signs_at_even_roots (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) (D : DenominatorInterlacing a)
    {e f : ℝ} (he0 : 0 ≤ e) (heo : e < D.o₁) (hof : D.o₁ < f) (hfo : f < D.o₂)
    (he : numeratorEven b e = 0) (hf : numeratorEven b f = 0) :
    0 < numeratorOdd b e ∧ numeratorOdd b f < 0 := by
  have hoapos : 0 < oddPart a e := by
    rw [D.odd_eval]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr heo)
      (sub_neg.mpr (heo.trans (D.o₁_lt_e₂.trans D.e₂_lt_o₂)))
  have hoaneg : oddPart a f < 0 := by
    rw [D.odd_eval]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hof) (sub_neg.mpr hfo)
  have hfpos : 0 < f := (D.e₁_pos.trans D.e₁_lt_o₁).trans hof
  have hfn : numeratorOdd b f ≠ 0 := fun ho =>
    K.no_common_positive_numerator_root hK hwidth hb hw hfpos hf ho
  have hff := hw a ha f hfpos.le
  simp only [generalPairing, hf, zero_mul, zero_add] at hff
  have hfnonpos : numeratorOdd b f ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge hff) (mul_neg_of_pos_of_neg hfpos
      (mul_neg_of_pos_of_neg (lt_of_not_ge h) hoaneg))
  refine ⟨?_, lt_of_le_of_ne hfnonpos hfn⟩
  by_cases hezero : e = 0
  · rw [hezero]
    simpa [numeratorOdd] using (K.weak_numerator_coefficients hK hwidth hb hb0 hw).2.2.2.1
  · have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm hezero)
    have hen : numeratorOdd b e ≠ 0 := fun ho =>
      K.no_common_positive_numerator_root hK hwidth hb hw hepos he ho
    have hee := hw a ha e he0
    simp only [generalPairing, he, zero_mul, zero_add] at hee
    have hepos' := (mul_nonneg_iff_of_pos_right hoapos).mp
      ((mul_nonneg_iff_of_pos_left hepos).mp hee)
    exact lt_of_le_of_ne hepos' (Ne.symm hen)

structure QuinticNumeratorInterlacing (b : Vec6) where
  e : ℝ
  k : ℝ
  f : ℝ
  l : ℝ
  e_nonneg : 0 ≤ e
  e_lt_k : e < k
  k_lt_f : k < f
  f_lt_l : f < l
  even_factor : numeratorEvenPoly b = C (b 1) * ((X - C e) * (X - C f))
  odd_factor : numeratorOddPoly b = C (b 0) * ((X - C k) * (X - C l))

structure QuarticNumeratorInterlacing (b : Vec6) where
  e : ℝ
  k : ℝ
  f : ℝ
  e_nonneg : 0 ≤ e
  e_lt_k : e < k
  k_lt_f : k < f
  even_factor : numeratorEvenPoly b = C (b 1) * ((X - C e) * (X - C f))
  odd_factor : numeratorOddPoly b = C (-(b 2)) * (X - C k)

theorem Box5.weak_quintic_interlacing (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 < b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    Nonempty (QuinticNumeratorInterlacing b) := by
  obtain ⟨D⟩ := denominator_interlacing (hK K.lower K.lower_mem)
  obtain ⟨e,f,he0,heo,hof,hfo,hEf⟩ := K.weak_even_root_locations hK hwidth hb hw K.lower_mem D
  obtain ⟨k,l,hek,hke,hel,hOf⟩ := K.weak_quintic_odd_root_locations
    hK hwidth hb hb0 hw K.lower_mem D
  have hE (t : ℝ) : numeratorEven b t = b 1 * ((t-e)*(t-f)) := by
    have h := congrArg (fun p : ℝ[X] => p.eval t) hEf
    simpa only [numeratorEvenPoly_eval, eval_mul, eval_sub, eval_C, eval_X] using h
  have hO (t : ℝ) : numeratorOdd b t = b 0 * ((t-k)*(t-l)) := by
    have h := congrArg (fun p : ℝ[X] => p.eval t) hOf
    simpa only [numeratorOddPoly_eval, eval_mul, eval_sub, eval_C, eval_X] using h
  obtain ⟨hOe,hOf'⟩ := K.odd_signs_at_even_roots hK hwidth hb hb0.le hw K.lower_mem D
    he0 heo hof hfo (by simp [hE]) (by simp [hE])
  have hel' : e < l := heo.trans (D.o₁_lt_e₂.trans hel)
  have hkl : k < l := hke.trans hel
  have hek' : e < k := by
    by_contra h
    have hp : (e-k)*(e-l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (le_of_not_gt h)) (sub_nonpos.mpr hel'.le)
    rw [hO] at hOe
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hb0.le hp)) hOe
  have hkf : k < f := by
    by_contra h
    have hfkle : f ≤ k := le_of_not_gt h
    have hp : 0 ≤ (f-k)*(f-l) := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hfkle) (sub_nonpos.mpr (hfkle.trans hkl.le))
    rw [hO] at hOf'
    exact (not_lt_of_ge (mul_nonneg hb0.le hp)) hOf'
  have hfl : f < l := by
    by_contra h
    have hlf : l ≤ f := le_of_not_gt h
    have hp : 0 ≤ (f-k)*(f-l) := mul_nonneg
      (sub_nonneg.mpr (hkl.le.trans hlf)) (sub_nonneg.mpr hlf)
    rw [hO] at hOf'
    exact (not_lt_of_ge (mul_nonneg hb0.le hp)) hOf'
  exact ⟨⟨e,k,f,l,he0,hek',hkf,hfl,hEf,hOf⟩⟩

theorem Box5.weak_quartic_interlacing (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : b 0 = 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    Nonempty (QuarticNumeratorInterlacing b) := by
  obtain ⟨D⟩ := denominator_interlacing (hK K.lower K.lower_mem)
  obtain ⟨e,f,he0,heo,hof,hfo,hEf⟩ := K.weak_even_root_locations hK hwidth hb hw K.lower_mem D
  obtain ⟨k,hek,hke,hOf⟩ := K.weak_quartic_odd_root_location
    hK hwidth hb hb0 hw K.lower_mem D
  have hE (t : ℝ) : numeratorEven b t = b 1 * ((t-e)*(t-f)) := by
    have h := congrArg (fun p : ℝ[X] => p.eval t) hEf
    simpa only [numeratorEvenPoly_eval, eval_mul, eval_sub, eval_C, eval_X] using h
  have hO (t : ℝ) : numeratorOdd b t = -(b 2) * (t-k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval t) hOf
    simpa only [numeratorOddPoly_eval, eval_mul, eval_sub, eval_C, eval_X] using h
  have hb0n : 0 ≤ b 0 := by rw [hb0]
  have hb2 := (K.weak_numerator_coefficients hK hwidth hb hb0n hw).2.1
  obtain ⟨hOe,hOf'⟩ := K.odd_signs_at_even_roots hK hwidth hb hb0n hw K.lower_mem D
    he0 heo hof hfo (by simp [hE]) (by simp [hE])
  have hek' : e < k := by
    by_contra h
    rw [hO] at hOe
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb2.le)
      (sub_nonneg.mpr (le_of_not_gt h)))) hOe
  have hkf : k < f := by
    by_contra h
    rw [hO] at hOf'
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb2.le)
      (sub_nonpos.mpr (le_of_not_gt h)))) hOf'
  exact ⟨⟨e,k,f,he0,hek',hkf,hEf,hOf⟩⟩

end
end SPR.N5.Direct
