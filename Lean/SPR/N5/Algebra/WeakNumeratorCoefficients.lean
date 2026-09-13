import SPR.N5.Algebra.WeakContactComponents

/-!
# WeakNumeratorCoefficients

论文 §4.1–4.2：非负性的代数后果、分子零点及互素性。
由分母根处符号推得分子系数的严格符号和可能的实际次数。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial

theorem Box5.weak_signs_at_interlacing (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {a : Poly5} (ha : K.Contains a) (D : DenominatorInterlacing a) :
    0 < numeratorOdd b D.e₁ ∧ numeratorOdd b D.e₂ < 0 ∧
      numeratorEven b D.o₁ < 0 ∧ 0 < numeratorEven b D.o₂ := by
  have hnO (t : ℝ) (ht : 0 < t) (hE : evenPart a t = 0) : numeratorOdd b t ≠ 0 := by
    intro ho
    have hc : generalPairing a b t = 0 := by simp [generalPairing, hE, ho]
    exact K.positive_contact_odd_ne_zero hK hwidth hb hw ha ht hc ho
  have hnE (t : ℝ) (ht : 0 < t) (hO : oddPart a t = 0) : numeratorEven b t ≠ 0 := by
    intro he
    have hc : generalPairing a b t = 0 := by simp [generalPairing, hO, he]
    exact K.positive_contact_even_ne_zero hK hwidth hb hw ha ht hc he
  have ho1 := D.e₁_pos.trans D.e₁_lt_o₁
  have he2 := ho1.trans D.o₁_lt_e₂
  have ho2 := he2.trans D.e₂_lt_o₂
  have h1 := hw a ha D.e₁ D.e₁_pos.le
  have h2 := hw a ha D.e₂ he2.le
  have h3 := hw a ha D.o₁ ho1.le
  have h4 := hw a ha D.o₂ ho2.le
  simp only [generalPairing, D.roots.1, mul_zero, zero_add] at h1
  simp only [generalPairing, D.roots.2.2.1, mul_zero, zero_add] at h2
  simp only [generalPairing, D.roots.2.1, mul_zero, add_zero] at h3
  simp only [generalPairing, D.roots.2.2.2, mul_zero, add_zero] at h4
  have h1' := (mul_nonneg_iff_of_pos_right D.odd_e₁_pos).mp
    ((mul_nonneg_iff_of_pos_left D.e₁_pos).mp h1)
  have h2' : numeratorOdd b D.e₂ ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge ((mul_nonneg_iff_of_pos_left he2).mp h2))
      (mul_neg_of_pos_of_neg (lt_of_not_ge h) D.odd_e₂_neg)
  have ha1 := (quintic_coefficients_pos (hK a ha)).1
  have h3' : numeratorEven b D.o₁ ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge h3) (mul_neg_of_pos_of_neg (lt_of_not_ge h) (D.even_o₁_neg ha1))
  have h4' := (mul_nonneg_iff_of_pos_right (D.even_o₂_pos ha1)).mp h4
  exact ⟨lt_of_le_of_ne h1' (Ne.symm (hnO _ D.e₁_pos D.roots.1)),
    lt_of_le_of_ne h2' (hnO _ he2 D.roots.2.2.1),
    lt_of_le_of_ne h3' (hnE _ ho1 D.roots.2.1),
    lt_of_le_of_ne h4' (Ne.symm (hnE _ ho2 D.roots.2.2.2))⟩

theorem quadratic_leading_pos_of_signs {u v w x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hw : 0 ≤ w) (hqx : u*x^2-v*x+w < 0) (hqy : 0 < u*y^2-v*y+w) : 0 < u := by
  by_contra hu
  have hu' : u ≤ 0 := le_of_not_gt hu
  have hy := hx.trans hxy
  have hright : (y-x)*(u*x*y-w) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hxy.le) (sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hu' hx.le) hy.le).trans hw))
  have hid : (y-x)*(u*x*y-w) = x*(u*y^2-v*y+w)-y*(u*x^2-v*x+w) := by ring
  rw [hid] at hright
  have hp := mul_pos hx hqy
  have hn := mul_neg_of_pos_of_neg hy hqx
  linarith

theorem quadratic_constant_pos_of_signs {u v w x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hu : 0 ≤ u) (hqx : 0 < u*x^2-v*x+w) (hqy : u*y^2-v*y+w < 0) : 0 < w := by
  by_contra hw
  have hw' : w ≤ 0 := le_of_not_gt hw
  have hy := hx.trans hxy
  have hright : 0 ≤ (y-x)*(u*x*y-w) := mul_nonneg
    (sub_nonneg.mpr hxy.le) (sub_nonneg.mpr (hw'.trans
      (mul_nonneg (mul_nonneg hu hx.le) hy.le)))
  have hid : (y-x)*(u*x*y-w) = x*(u*y^2-v*y+w)-y*(u*x^2-v*x+w) := by ring
  rw [hid] at hright
  have hp := mul_pos hy hqx
  have hn := mul_neg_of_pos_of_neg hx hqy
  linarith

theorem quadratic_middle_pos_of_signs {u v w x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hu : 0 ≤ u) (hqx : 0 < u*x^2-v*x+w) (hqy : u*y^2-v*y+w < 0) : 0 < v := by
  by_contra hv
  have hv' : v ≤ 0 := le_of_not_gt hv
  have hy := hx.trans hxy
  have hright : 0 ≤ (y-x)*(u*(y+x)-v) := mul_nonneg
    (sub_nonneg.mpr hxy.le) (sub_nonneg.mpr (hv'.trans
      (mul_nonneg hu (add_nonneg hy.le hx.le))))
  have hid : (y-x)*(u*(y+x)-v) = (u*y^2-v*y+w)-(u*x^2-v*x+w) := by ring
  rw [hid] at hright
  linarith

/-- All actual numerator coefficients except the optional leading and constant
terms are strictly positive, obtained without a positive-real analytic theorem. -/
theorem Box5.weak_numerator_coefficients (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    0 < b 1 ∧ 0 < b 2 ∧ 0 < b 3 ∧ 0 < b 4 ∧ 0 ≤ b 5 := by
  obtain ⟨D⟩ := denominator_interlacing (hK K.lower K.lower_mem)
  obtain ⟨hO1,hO2,hE1,hE2⟩ := K.weak_signs_at_interlacing hK hwidth hb hw K.lower_mem D
  have hb5 := weak_numerator_constant_nonneg (hK K.lower K.lower_mem) (hw K.lower K.lower_mem)
  have ho1 := D.e₁_pos.trans D.e₁_lt_o₁
  have ho12 := D.o₁_lt_e₂.trans D.e₂_lt_o₂
  have he12 := D.e₁_lt_o₁.trans D.o₁_lt_e₂
  have hb1 := quadratic_leading_pos_of_signs ho1 ho12 hb5 hE1 hE2
  have hb2 := quadratic_middle_pos_of_signs D.e₁_pos he12 hb0 hO1 hO2
  have hb4 := quadratic_constant_pos_of_signs D.e₁_pos he12 hb0 hO1 hO2
  have hb3 : 0 < b 3 := by
    by_contra h
    have h3 : b 3 ≤ 0 := le_of_not_gt h
    have hprod := mul_nonpos_of_nonpos_of_nonneg h3 ho1.le
    have hpos := mul_nonneg hb1.le (sq_nonneg D.o₁)
    change b 1*D.o₁^2-b 3*D.o₁+b 5 < 0 at hE1
    linarith
  exact ⟨hb1,hb2,hb3,hb4,hb5⟩

theorem numeratorPoly_degree_four {b : Vec6} (hb0 : b 0 = 0) (hb1 : b 1 ≠ 0) :
    (numeratorPoly b).natDegree = 4 := by
  unfold numeratorPoly
  rw [hb0]
  simp only [map_zero, zero_mul, zero_add]
  compute_degree!

theorem Box5.weak_numerator_degree_four_or_five (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    (numeratorPoly b).natDegree = 4 ∨ (numeratorPoly b).natDegree = 5 := by
  have hb1 := (K.weak_numerator_coefficients hK hwidth hb hb0 hw).1
  by_cases he : b 0 = 0
  · exact Or.inl (numeratorPoly_degree_four he (ne_of_gt hb1))
  · exact Or.inr (numeratorPoly_degree b he)

end
end SPR.N5.Direct
