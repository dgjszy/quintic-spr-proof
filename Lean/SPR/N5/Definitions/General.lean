import SPR.N5.Definitions.Frequency

/-! Six unrestricted real numerator coefficients, including weak quartic numerators.
## 与论文的对应

论文 §1–2：基本对象、精确主命题与虚轴分解。
允许首项系数为零的六维分子系数；把频域配对写成线性泛函并紧化频率。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Complex

/-- 分子从五次项到常数项的六个系数；不预先假设首项非零。 -/
abbrev Vec6 := Fin 6 → ℝ

/-- 由六个实系数重建分子，实际次数可能低于五。 -/
def numeratorPoly (b : Vec6) : ℝ[X] :=
  C (b 0) * X ^ 5 + C (b 1) * X ^ 4 + C (b 2) * X ^ 3 +
    C (b 3) * X ^ 2 + C (b 4) * X + C (b 5)

/-- 论文中的 E_b(t)=b₁t²−b₃t+b₅。 -/
def numeratorEven (b : Vec6) (t : ℝ) : ℝ := b 1 * t ^ 2 - b 3 * t + b 5

/-- 论文中的 O_b(t)=b₀t²−b₂t+b₄。 -/
def numeratorOdd (b : Vec6) (t : ℝ) : ℝ := b 0 * t ^ 2 - b 2 * t + b 4

/-- 论文中的 P_{a,b}(t)=E_b(t)E_a(t)+t O_b(t)O_a(t)。 -/
def generalPairing (a : Poly5) (b : Vec6) (t : ℝ) : ℝ :=
  numeratorEven b t * evenPart a t + t * (numeratorOdd b t * oddPart a t)

theorem numeratorPoly_degree (b : Vec6) (hb : b 0 ≠ 0) :
    (numeratorPoly b).natDegree = 5 := by
  unfold numeratorPoly
  compute_degree!

theorem numerator_frequency_eq (b : Vec6) (ω : ℝ) :
    eval (I * (ω : ℂ)) ((numeratorPoly b).map (algebraMap ℝ ℂ)) =
      (numeratorEven b (ω ^ 2) : ℂ) + I * (ω : ℂ) * (numeratorOdd b (ω ^ 2) : ℂ) := by
  simp only [numeratorPoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    numeratorEven, numeratorOdd, ofReal_add, ofReal_sub, ofReal_mul, ofReal_pow]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem general_real_ratio_eq (a : Poly5) (b : Vec6) (ω : ℝ) :
    (eval (I * (ω : ℂ)) ((numeratorPoly b).map (algebraMap ℝ ℂ)) /
      frequencyValue a ω).re = generalPairing a b (ω ^ 2) /
        Complex.normSq (frequencyValue a ω) := by
  rw [Complex.div_re, frequencyValue_re, frequencyValue_im, numerator_frequency_eq]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_im, I_im, ofReal_im,
    zero_mul, one_mul, mul_zero, sub_zero, zero_add, add_im, add_zero]
  unfold generalPairing
  rw [← add_div]
  congr 1
  ring

theorem general_frequencySPR_iff {a : Poly5} (ha : IsHurwitz a.toPoly) (b : Vec6) :
    FrequencySPR a.toPoly (numeratorPoly b) ↔
      ∀ t : ℝ, 0 ≤ t → 0 < generalPairing a b t := by
  have hω (ω : ℝ) :
      0 < (eval (I * (ω : ℂ)) ((numeratorPoly b).map (algebraMap ℝ ℂ)) /
        frequencyValue a ω).re ↔ 0 < generalPairing a b (ω ^ 2) := by
    rw [general_real_ratio_eq]
    exact div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (hurwitz_frequencyValue_ne_zero ha ω))
  constructor
  · intro h t ht
    simpa only [Real.sq_sqrt ht] using (hω (Real.sqrt t)).mp (h (Real.sqrt t))
  · intro h ω
    exact (hω ω).mpr (h (ω ^ 2) (sq_nonneg ω))

theorem Box5.general_exists_corner_le {K : Box5} {a : Poly5} (ha : K.Contains a)
    (b : Vec6) {t : ℝ} (ht : 0 ≤ t) :
    ∃ c : Corner, generalPairing (K.corner c) b t ≤ generalPairing a b t := by
  rcases K.component_bounds ha ht with ⟨hel, heu, hol, hou⟩
  by_cases he : 0 ≤ numeratorEven b t
  · have hE := mul_le_mul_of_nonneg_left hel he
    by_cases ho : 0 ≤ numeratorOdd b t
    · have hO := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hol ho) ht
      exact ⟨.D, add_le_add hE hO⟩
    · have hO := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonpos_left hou (le_of_lt (lt_of_not_ge ho))) ht
      exact ⟨.C, add_le_add hE hO⟩
  · have hE := mul_le_mul_of_nonpos_left heu (le_of_lt (lt_of_not_ge he))
    by_cases ho : 0 ≤ numeratorOdd b t
    · have hO := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hol ho) ht
      exact ⟨.A, add_le_add hE hO⟩
    · have hO := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonpos_left hou (le_of_lt (lt_of_not_ge ho))) ht
      exact ⟨.B, add_le_add hE hO⟩

theorem Box5.general_pairing_pos_iff_corners (K : Box5) (b : Vec6) :
    (∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 < generalPairing a b t) ↔
      ∀ c : Corner, ∀ t : ℝ, 0 ≤ t → 0 < generalPairing (K.corner c) b t := by
  constructor
  · intro h c
    exact h _ (K.corner_mem c)
  · intro h a ha t ht
    obtain ⟨c, hc⟩ := K.general_exists_corner_le ha b ht
    exact lt_of_lt_of_le (h c t ht) hc

theorem Box5.general_pairing_nonneg_iff_corners (K : Box5) (b : Vec6) :
    (∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ↔
      ∀ c : Corner, ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing (K.corner c) b t := by
  constructor
  · intro h c
    exact h _ (K.corner_mem c)
  · intro h a ha t ht
    obtain ⟨c, hc⟩ := K.general_exists_corner_le ha b ht
    exact (h c t ht).trans hc

/-- 使 P_{a,b}(t)=b·F(a,t) 的六维特征向量。 -/
def feature (a : Poly5) (t : ℝ) : Vec6 :=
  ![t ^ 3 * oddPart a t, t ^ 2 * evenPart a t, -(t ^ 2 * oddPart a t),
    -(t * evenPart a t), t * oddPart a t, evenPart a t]

/-- 六维实向量的标准内积。 -/
def dot6 (b v : Vec6) : ℝ := ∑ i, b i * v i

theorem dot6_feature (a : Poly5) (b : Vec6) (t : ℝ) :
    dot6 b (feature a t) = generalPairing a b t := by
  simp [dot6, feature, Fin.sum_univ_succ, generalPairing, numeratorEven, numeratorOdd]
  ring

def compactEven (a : Poly5) (x : ℝ) : ℝ :=
  a.a1 * x ^ 2 - a.a3 * x * (1 - x) + a.a5 * (1 - x) ^ 2

def compactOdd (a : Poly5) (x : ℝ) : ℝ :=
  x ^ 2 - a.a2 * x * (1 - x) + a.a4 * (1 - x) ^ 2

/-- Polynomial compactification; x = 1 represents infinite frequency. -/
def compactFeature (a : Poly5) (x : ℝ) : Vec6 :=
  ![x ^ 3 * compactOdd a x, x ^ 2 * (1 - x) * compactEven a x,
    -(x ^ 2 * (1 - x) * compactOdd a x), -(x * (1 - x) ^ 2 * compactEven a x),
    x * (1 - x) ^ 2 * compactOdd a x, (1 - x) ^ 3 * compactEven a x]

theorem compactFeature_at_one (a : Poly5) :
    compactFeature a 1 = ![1, 0, 0, 0, 0, 0] := by
  simp [compactFeature, compactEven, compactOdd]

theorem dot6_at_infinity (a : Poly5) (b : Vec6) :
    dot6 b (compactFeature a 1) = b 0 := by
  simp [compactFeature_at_one, dot6, Fin.sum_univ_succ]

theorem continuous_compactFeature (a : Poly5) : Continuous (compactFeature a) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [compactFeature, compactEven, compactOdd] <;> fun_prop

theorem compactFeature_eq (a : Poly5) {x : ℝ} (hx : x ≠ 1) :
    compactFeature a x = (1 - x) ^ 5 • feature a (x / (1 - x)) := by
  have hd : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  ext i
  fin_cases i <;>
    simp [compactFeature, feature, compactEven, compactOdd, evenPart, oddPart,
      Pi.smul_apply, smul_eq_mul] <;> field_simp <;> ring

theorem dot6_smul (b v : Vec6) (r : ℝ) : dot6 b (r • v) = r * dot6 b v := by
  simp only [dot6, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem compact_pairing_eq (a : Poly5) (b : Vec6) {x : ℝ} (hx : x ≠ 1) :
    dot6 b (compactFeature a x) = (1 - x) ^ 5 * generalPairing a b (x / (1 - x)) := by
  rw [compactFeature_eq a hx, dot6_smul, dot6_feature]

theorem compact_pairing_pos_iff (a : Poly5) (b : Vec6) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < dot6 b (compactFeature a x)) ↔
      0 < b 0 ∧ ∀ t : ℝ, 0 ≤ t → 0 < generalPairing a b t := by
  constructor
  · intro h
    refine ⟨by simpa only [dot6_at_infinity] using h 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
    intro t ht
    have hd : 0 < 1 + t := by linarith
    have hx : t / (1 + t) < 1 := (div_lt_one hd).mpr (by linarith)
    have hc := h (t / (1 + t)) ⟨div_nonneg ht hd.le, hx.le⟩
    rw [compact_pairing_eq a b (ne_of_lt hx)] at hc
    have hid : t / (1 + t) / (1 - t / (1 + t)) = t := by field_simp; ring
    rw [hid] at hc
    exact (mul_pos_iff_of_pos_left (pow_pos (sub_pos.mpr hx) 5)).mp hc
  · rintro ⟨hb, h⟩ x ⟨hx0, hx1⟩
    by_cases hx : x = 1
    · simpa only [hx, dot6_at_infinity] using hb
    · have hlt : x < 1 := lt_of_le_of_ne hx1 hx
      rw [compact_pairing_eq a b hx]
      exact mul_pos (pow_pos (sub_pos.mpr hlt) 5)
        (h _ (div_nonneg hx0 (sub_nonneg.mpr hx1)))

end
end SPR.N5.Direct
