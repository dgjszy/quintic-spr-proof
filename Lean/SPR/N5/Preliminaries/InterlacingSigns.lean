import SPR.N5.Preliminaries.HermiteBiehler

/-!
# InterlacingSigns

论文 §2：Hurwitz 稳定性、零点交错及统一分母零点区间。
将交错结构转换为各根处的取值符号及线性组合约束。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial

theorem DenominatorInterlacing.even_eval {a : Poly5} (D : DenominatorInterlacing a) (t : ℝ) :
    evenPart a t = a.a1 * ((t - D.e₁) * (t - D.e₂)) := by
  have h := congrArg (fun p : ℝ[X] => p.eval t) D.even_factor
  simpa [denominatorEvenPoly, evenPart] using h

theorem DenominatorInterlacing.odd_eval {a : Poly5} (D : DenominatorInterlacing a) (t : ℝ) :
    oddPart a t = (t - D.o₁) * (t - D.o₂) := by
  have h := congrArg (fun p : ℝ[X] => p.eval t) D.odd_factor
  simpa [denominatorOddPoly, oddPart] using h

theorem DenominatorInterlacing.odd_e₁_pos {a : Poly5} (D : DenominatorInterlacing a) :
    0 < oddPart a D.e₁ := by
  rw [D.odd_eval]
  exact mul_pos_of_neg_of_neg (sub_neg.mpr D.e₁_lt_o₁)
    (sub_neg.mpr (D.e₁_lt_o₁.trans (D.o₁_lt_e₂.trans D.e₂_lt_o₂)))

theorem DenominatorInterlacing.odd_e₂_neg {a : Poly5} (D : DenominatorInterlacing a) :
    oddPart a D.e₂ < 0 := by
  rw [D.odd_eval]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr D.o₁_lt_e₂) (sub_neg.mpr D.e₂_lt_o₂)

theorem DenominatorInterlacing.even_o₁_neg {a : Poly5} (D : DenominatorInterlacing a)
    (ha1 : 0 < a.a1) : evenPart a D.o₁ < 0 := by
  rw [D.even_eval]
  exact mul_neg_of_pos_of_neg ha1
    (mul_neg_of_pos_of_neg (sub_pos.mpr D.e₁_lt_o₁) (sub_neg.mpr D.o₁_lt_e₂))

theorem DenominatorInterlacing.even_o₂_pos {a : Poly5} (D : DenominatorInterlacing a)
    (ha1 : 0 < a.a1) : 0 < evenPart a D.o₂ := by
  rw [D.even_eval]
  exact mul_pos ha1 (mul_pos
    (sub_pos.mpr (D.e₁_lt_o₁.trans (D.o₁_lt_e₂.trans D.e₂_lt_o₂)))
    (sub_pos.mpr D.e₂_lt_o₂))

theorem DenominatorInterlacing.roots {a : Poly5} (D : DenominatorInterlacing a) :
    evenPart a D.e₁ = 0 ∧ oddPart a D.o₁ = 0 ∧
      evenPart a D.e₂ = 0 ∧ oddPart a D.o₂ = 0 := by
  simp [D.even_eval, D.odd_eval]

theorem DenominatorInterlacing.even_derivative_ne_zero {a : Poly5}
    (D : DenominatorInterlacing a) (ha1 : a.a1 ≠ 0) {t : ℝ}
    (ht : evenPart a t = 0) : (denominatorEvenPoly a).derivative.eval t ≠ 0 := by
  have hroot : t = D.e₁ ∨ t = D.e₂ := by
    rw [D.even_eval] at ht
    simpa only [mul_eq_zero, ha1, false_or, sub_eq_zero] using ht
  rw [D.even_factor]
  rcases hroot with rfl | rfl <;>
    simp [derivative_mul, ha1, sub_eq_zero, ne_of_lt (D.e₁_lt_o₁.trans D.o₁_lt_e₂),
      ne_of_gt (D.e₁_lt_o₁.trans D.o₁_lt_e₂)]

theorem DenominatorInterlacing.odd_derivative_ne_zero {a : Poly5}
    (D : DenominatorInterlacing a) {t : ℝ} (ht : oddPart a t = 0) :
    (denominatorOddPoly a).derivative.eval t ≠ 0 := by
  have hroot : t = D.o₁ ∨ t = D.o₂ := by
    simpa [D.odd_eval, sub_eq_zero] using ht
  rw [D.odd_factor]
  rcases hroot with rfl | rfl <;>
    simp [derivative_mul, sub_eq_zero, ne_of_lt (D.o₁_lt_e₂.trans D.e₂_lt_o₂),
      ne_of_gt (D.o₁_lt_e₂.trans D.e₂_lt_o₂)]

/-- A linear numerator cannot have nonnegative pairing with a Hurwitz quintic
unless it is zero. This uses only signs at the four interlacing roots. -/
theorem linear_weak_pairing_zero {a : Poly5} (ha : IsHurwitz a.toPoly) (c d : ℝ)
    (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ c * evenPart a t + t * d * oddPart a t) :
    c = 0 ∧ d = 0 := by
  obtain ⟨D⟩ := denominator_interlacing ha
  have ha1 := (quintic_coefficients_pos ha).1
  have ho1 : 0 < D.o₁ := D.e₁_pos.trans D.e₁_lt_o₁
  have he2 : 0 < D.e₂ := ho1.trans D.o₁_lt_e₂
  have ho2 : 0 < D.o₂ := he2.trans D.e₂_lt_o₂
  have hc1 := hw D.o₁ ho1.le
  have hc2 := hw D.o₂ ho2.le
  rw [D.roots.2.1, mul_zero, add_zero] at hc1
  rw [D.roots.2.2.2, mul_zero, add_zero] at hc2
  have hcpos : 0 ≤ c := (mul_nonneg_iff_of_pos_right (D.even_o₂_pos ha1)).mp hc2
  have hcneg : c ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge hc1) (mul_neg_of_pos_of_neg (lt_of_not_ge h) (D.even_o₁_neg ha1))
  have hc : c = 0 := le_antisymm hcneg hcpos
  have hd1 := hw D.e₁ D.e₁_pos.le
  have hd2 := hw D.e₂ he2.le
  simp only [hc, zero_mul, zero_add] at hd1 hd2
  have hdpos : 0 ≤ d := by
    have h : 0 ≤ D.e₁ * d := (mul_nonneg_iff_of_pos_right D.odd_e₁_pos).mp hd1
    exact (mul_nonneg_iff_of_pos_left D.e₁_pos).mp h
  have hdneg : d ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge hd2) (mul_neg_of_pos_of_neg
      (mul_pos he2 (lt_of_not_ge h)) D.odd_e₂_neg)
  exact ⟨hc, le_antisymm hdneg hdpos⟩

end
end SPR.N5.Direct
