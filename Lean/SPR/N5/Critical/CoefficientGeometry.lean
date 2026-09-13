import SPR.N5.Algebra.WeakCoprime

/-!
# CoefficientGeometry

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
用系数向量描述紧区间族、小幅扩张及系数投影，为稳定扩张提供几何界。
-/

namespace SPR.N5.Direct

noncomputable section
open Polynomial Set

abbrev Coeff5 := Fin 5 → ℝ
def coefficients5 (a : Poly5) : Coeff5 := ![a.a1,a.a2,a.a3,a.a4,a.a5]
def polynomial5 (v : Coeff5) : Poly5 := ⟨v 0,v 1,v 2,v 3,v 4⟩

theorem polynomial5_coefficients5 (a : Poly5) : polynomial5 (coefficients5 a) = a := by
  cases a
  rfl

theorem coefficients5_polynomial5 (v : Coeff5) : coefficients5 (polynomial5 v) = v := by
  funext i
  fin_cases i <;> rfl

theorem Box5.coefficients_le (K : Box5) : coefficients5 K.lower ≤ coefficients5 K.upper := by
  intro i
  fin_cases i <;> simp [coefficients5, K.h1, K.h2, K.h3, K.h4, K.h5]

def Box5.coefficientSet (K : Box5) : Set Coeff5 :=
  Icc (coefficients5 K.lower) (coefficients5 K.upper)

theorem Box5.mem_coefficientSet (K : Box5) (v : Coeff5) :
    v ∈ K.coefficientSet ↔ K.Contains (polynomial5 v) := by
  simp only [coefficientSet, mem_Icc, Pi.le_def, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true, Contains, polynomial5, coefficients5,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  tauto

theorem Box5.compact_coefficientSet (K : Box5) : IsCompact K.coefficientSet := isCompact_Icc

theorem Box5.coefficients_mem (K : Box5) {a : Poly5} (ha : K.Contains a) :
    coefficients5 a ∈ K.coefficientSet := by
  rw [K.mem_coefficientSet, polynomial5_coefficients5]
  exact ha

def Box5.expand (K : Box5) (ε : ℝ) (hε : 0 ≤ ε) : Box5 where
  lower := polynomial5 (fun i => coefficients5 K.lower i - ε)
  upper := polynomial5 (fun i => coefficients5 K.upper i + ε)
  h1 := by have h := K.h1; dsimp [polynomial5, coefficients5]; linarith
  h2 := by have h := K.h2; dsimp [polynomial5, coefficients5]; linarith
  h3 := by have h := K.h3; dsimp [polynomial5, coefficients5]; linarith
  h4 := by have h := K.h4; dsimp [polynomial5, coefficients5]; linarith
  h5 := by have h := K.h5; dsimp [polynomial5, coefficients5]; linarith

theorem Box5.expand_lower_coefficients (K : Box5) (ε : ℝ) (hε : 0 ≤ ε) :
    coefficients5 (K.expand ε hε).lower = fun i => coefficients5 K.lower i - ε :=
  coefficients5_polynomial5 _

theorem Box5.expand_upper_coefficients (K : Box5) (ε : ℝ) (hε : 0 ≤ ε) :
    coefficients5 (K.expand ε hε).upper = fun i => coefficients5 K.upper i + ε :=
  coefficients5_polynomial5 _

theorem Box5.expand_fullWidth (K : Box5) {ε : ℝ} (hε : 0 < ε) :
    (K.expand ε hε.le).FullWidth := by
  have h1 := K.h1
  have h2 := K.h2
  have h3 := K.h3
  have h4 := K.h4
  have h5 := K.h5
  dsimp [FullWidth, expand, polynomial5, coefficients5]
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem Box5.expand_subset (K : Box5) {ε : ℝ} (hε : 0 ≤ ε) {a : Poly5}
    (ha : K.Contains a) : (K.expand ε hε).Contains a := by
  rw [← polynomial5_coefficients5 a, ← (K.expand ε hε).mem_coefficientSet]
  have hm := K.coefficients_mem ha
  change coefficients5 (K.expand ε hε).lower ≤ coefficients5 a ∧
    coefficients5 a ≤ coefficients5 (K.expand ε hε).upper
  rw [K.expand_lower_coefficients, K.expand_upper_coefficients]
  exact ⟨fun i => (sub_le_self _ hε).trans (hm.1 i),
    fun i => (hm.2 i).trans (le_add_of_nonneg_right hε)⟩

def Box5.coefficientBound (K : Box5) : ℝ :=
  max ‖coefficients5 K.lower‖ ‖coefficients5 K.upper‖ + 1

theorem Box5.coefficientBound_pos (K : Box5) : 0 < K.coefficientBound := by
  unfold coefficientBound
  have h := norm_nonneg (coefficients5 K.lower)
  positivity

theorem Box5.expanded_norm_bound (K : Box5) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {v : Coeff5} (hv : v ∈ (K.expand ε hε).coefficientSet) : ‖v‖ ≤ K.coefficientBound := by
  apply (pi_norm_le_iff_of_nonneg K.coefficientBound_pos.le).mpr
  intro i
  have hl := hv.1 i
  have hu := hv.2 i
  rw [K.expand_lower_coefficients] at hl
  rw [K.expand_upper_coefficients] at hu
  have hli := norm_le_pi_norm (coefficients5 K.lower) i
  have hui := norm_le_pi_norm (coefficients5 K.upper) i
  have habsl := (abs_le.mp (show |coefficients5 K.lower i| ≤ ‖coefficients5 K.lower‖ from hli)).1
  have habsu := (abs_le.mp (show |coefficients5 K.upper i| ≤ ‖coefficients5 K.upper‖ from hui)).2
  rw [Real.norm_eq_abs, abs_le]
  unfold coefficientBound
  have hmaxl := le_max_left ‖coefficients5 K.lower‖ ‖coefficients5 K.upper‖
  have hmaxu := le_max_right ‖coefficients5 K.lower‖ ‖coefficients5 K.upper‖
  constructor <;> linarith

def Box5.clipCoefficients (K : Box5) (v : Coeff5) : Coeff5 :=
  fun i => max (coefficients5 K.lower i) (min (coefficients5 K.upper i) (v i))

theorem Box5.clipCoefficients_mem (K : Box5) (v : Coeff5) :
    K.clipCoefficients v ∈ K.coefficientSet := by
  exact ⟨fun i => le_max_left _ _, fun i => max_le (K.coefficients_le i) (min_le_left _ _)⟩

theorem Box5.dist_clip_le (K : Box5) {ε : ℝ} (hε : 0 ≤ ε)
    {v : Coeff5} (hv : v ∈ (K.expand ε hε).coefficientSet) :
    dist v (K.clipCoefficients v) ≤ ε := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro i
  have hl := hv.1 i
  have hu := hv.2 i
  rw [K.expand_lower_coefficients] at hl
  rw [K.expand_upper_coefficients] at hu
  change |v i - max (coefficients5 K.lower i) (min (coefficients5 K.upper i) (v i))| ≤ ε
  have hlu := K.coefficients_le i
  by_cases hvl : v i < coefficients5 K.lower i
  · rw [min_eq_right (hvl.le.trans hlu), max_eq_left hvl.le, abs_of_nonpos (sub_nonpos.mpr hvl.le)]
    linarith
  · have hlv := le_of_not_gt hvl
    by_cases hvu : v i ≤ coefficients5 K.upper i
    · rw [min_eq_right hvu, max_eq_right hlv, sub_self, abs_zero]
      exact hε
    · have huv := le_of_not_ge hvu
      rw [min_eq_left huv, max_eq_right hlu, abs_of_nonneg (sub_nonneg.mpr huv)]
      linarith

theorem continuous_coefficient_eval : Continuous
    (fun p : Coeff5 × ℂ => ((polynomial5 p.1).toPoly.map (algebraMap ℝ ℂ)).eval p.2) := by
  simp only [polynomial5, Poly5.toPoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fun_prop

end
end SPR.N5.Direct
