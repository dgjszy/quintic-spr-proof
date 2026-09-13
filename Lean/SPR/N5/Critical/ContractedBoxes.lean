import SPR.N5.Critical.BoundarySupport

/-! An explicit stable path from a singleton to the given interval box.
The first-boundary-point argument is not included in this module.

## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
构造从单点到原区间族的收缩路径，并定义各系数区间均非退化的 FullWidth。
-/
namespace SPR.N5.Direct

noncomputable section
open Set

def interpolatePoly (a z : Poly5) (θ : ℝ) : Poly5 :=
  ⟨a.a1 + θ * (z.a1 - a.a1), a.a2 + θ * (z.a2 - a.a2),
    a.a3 + θ * (z.a3 - a.a3), a.a4 + θ * (z.a4 - a.a4), a.a5 + θ * (z.a5 - a.a5)⟩

theorem interpolatePoly_zero (a z : Poly5) : interpolatePoly a z 0 = a := by
  cases a; cases z; simp [interpolatePoly]

theorem interpolatePoly_one (a z : Poly5) : interpolatePoly a z 1 = z := by
  cases a; cases z; simp [interpolatePoly]

def Box5.contract (K : Box5) (θ : ℝ) (hθ : 0 ≤ θ) : Box5 where
  lower := K.lower
  upper := interpolatePoly K.lower K.upper θ
  h1 := le_add_of_nonneg_right (mul_nonneg hθ (sub_nonneg.mpr K.h1))
  h2 := le_add_of_nonneg_right (mul_nonneg hθ (sub_nonneg.mpr K.h2))
  h3 := le_add_of_nonneg_right (mul_nonneg hθ (sub_nonneg.mpr K.h3))
  h4 := le_add_of_nonneg_right (mul_nonneg hθ (sub_nonneg.mpr K.h4))
  h5 := le_add_of_nonneg_right (mul_nonneg hθ (sub_nonneg.mpr K.h5))

theorem contracted_upper_le {l u θ : ℝ} (hlu : l ≤ u) (hθ : θ ≤ 1) :
    l + θ * (u - l) ≤ u := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr hlu)]

theorem Box5.contract_subset (K : Box5) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {a : Poly5} (ha : (K.contract θ hθ).Contains a) : K.Contains a := by
  rcases ha with ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u⟩
  exact ⟨h1l, h1u.trans (contracted_upper_le K.h1 hθ1),
    h2l, h2u.trans (contracted_upper_le K.h2 hθ1),
    h3l, h3u.trans (contracted_upper_le K.h3 hθ1),
    h4l, h4u.trans (contracted_upper_le K.h4 hθ1),
    h5l, h5u.trans (contracted_upper_le K.h5 hθ1)⟩

theorem Box5.contract_hurwitz (K : Box5) (hK : K.RobustlyHurwitz)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : (K.contract θ hθ).RobustlyHurwitz :=
  fun a ha => hK a (K.contract_subset hθ hθ1 ha)

def Box5.FullWidth (K : Box5) : Prop :=
  K.lower.a1 < K.upper.a1 ∧ K.lower.a2 < K.upper.a2 ∧ K.lower.a3 < K.upper.a3 ∧
    K.lower.a4 < K.upper.a4 ∧ K.lower.a5 < K.upper.a5

theorem Box5.contract_fullWidth (K : Box5) (hK : K.FullWidth) {θ : ℝ} (hθ : 0 < θ) :
    (K.contract θ hθ.le).FullWidth := by
  rcases hK with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨lt_add_of_pos_right _ (mul_pos hθ (sub_pos.mpr h1)),
    lt_add_of_pos_right _ (mul_pos hθ (sub_pos.mpr h2)),
    lt_add_of_pos_right _ (mul_pos hθ (sub_pos.mpr h3)),
    lt_add_of_pos_right _ (mul_pos hθ (sub_pos.mpr h4)),
    lt_add_of_pos_right _ (mul_pos hθ (sub_pos.mpr h5))⟩

theorem Box5.contract_corner (K : Box5) (c : Corner) {θ : ℝ} (hθ : 0 ≤ θ) :
    (K.contract θ hθ).corner c = interpolatePoly K.lower (K.corner c) θ := by
  cases c <;> simp [contract, corner, interpolatePoly]

theorem Box5.contract_zero_corner (K : Box5) (c : Corner) :
    (K.contract 0 le_rfl).corner c = K.lower := by
  rw [K.contract_corner, interpolatePoly_zero]

theorem Box5.contract_one_corner (K : Box5) (c : Corner) :
    (K.contract 1 zero_le_one).corner c = K.corner c := by
  rw [K.contract_corner, interpolatePoly_one]

theorem Box5.lower_mem (K : Box5) : K.Contains K.lower := by
  simp [Contains, K.h1, K.h2, K.h3, K.h4, K.h5]

def monicCoefficients (a : Poly5) : Vec6 := ![1, a.a1, a.a2, a.a3, a.a4, a.a5]

theorem monic_generalPairing (a z : Poly5) (t : ℝ) :
    generalPairing a (monicCoefficients z) t = pairing a z t := by
  simp [generalPairing, monicCoefficients, numeratorEven, numeratorOdd, pairing, evenPart, oddPart]

theorem hurwitz_self_pairing_pos {a : Poly5} (ha : IsHurwitz a.toPoly) :
    ∀ t : ℝ, 0 ≤ t → 0 < pairing a a t := by
  apply (frequencySPR_iff_pairing_pos ha).mp
  intro ω
  change 0 < (frequencyValue a ω / frequencyValue a ω).re
  rw [div_self (hurwitz_frequencyValue_ne_zero ha ω)]
  norm_num

theorem Box5.contract_zero_separated (K : Box5) (hK : K.RobustlyHurwitz) :
    (0 : Vec6) ∉ (K.contract 0 le_rfl).featureHull := by
  apply (K.contract 0 le_rfl).separator_iff.mp
  refine ⟨monicCoefficients K.lower, by simp [monicCoefficients], ?_⟩
  apply ((K.contract 0 le_rfl).general_pairing_pos_iff_corners _).mpr
  intro c t ht
  rw [K.contract_zero_corner, monic_generalPairing]
  exact hurwitz_self_pairing_pos (hK _ K.lower_mem) t ht

theorem Box5.contract_one_hull (K : Box5) :
    (K.contract 1 zero_le_one).featureHull = K.featureHull := by
  unfold featureHull featureSet
  simp only [K.contract_one_corner]

/-- Joint continuity in the contraction parameter and compactified frequency. -/
theorem continuous_interpolated_feature (a z : Poly5) :
    Continuous (fun p : ℝ × ℝ => compactFeature (interpolatePoly a z p.1) p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    dsimp [compactFeature, compactEven, compactOdd, interpolatePoly] <;> fun_prop

end
end SPR.N5.Direct
