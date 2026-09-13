import Mathlib
import SPR.N5.Definitions.Basic

/-!
# Exact statement and frequency algebra for the direct SPR proof

The foundational module supplies only Hurwitz stability and monic quintic coefficients.
`RobustSPRStatement` states the exact target; `robustSPR` in `Main.lean` proves it.

## 与论文的对应

论文 §1–2：基本对象、精确主命题与虚轴分解。
精确给出区间族、全族全频率命题，并证明偶奇分解和四顶点约化。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Complex

/-- 实首一五次多项式的闭系数区间族；允许一个或多个区间退化为单点。 -/
structure Box5 where
  lower : Poly5
  upper : Poly5
  h1 : lower.a1 ≤ upper.a1
  h2 : lower.a2 ≤ upper.a2
  h3 : lower.a3 ≤ upper.a3
  h4 : lower.a4 ≤ upper.a4
  h5 : lower.a5 ≤ upper.a5

/-- 逐个系数落在给定闭区间内。 -/
def Box5.Contains (K : Box5) (a : Poly5) : Prop :=
  K.lower.a1 ≤ a.a1 ∧ a.a1 ≤ K.upper.a1 ∧
  K.lower.a2 ≤ a.a2 ∧ a.a2 ≤ K.upper.a2 ∧
  K.lower.a3 ≤ a.a3 ∧ a.a3 ≤ K.upper.a3 ∧
  K.lower.a4 ≤ a.a4 ∧ a.a4 ≤ K.upper.a4 ∧
  K.lower.a5 ≤ a.a5 ∧ a.a5 ≤ K.upper.a5

/-- 族内每个多项式均 Hurwitz 稳定。 -/
def Box5.RobustlyHurwitz (K : Box5) : Prop :=
  ∀ a : Poly5, K.Contains a → IsHurwitz a.toPoly

/-- The user's frequency condition, without an additional numerator-stability hypothesis. -/
def FrequencySPR (a b : ℝ[X]) : Prop :=
  ∀ ω : ℝ, 0 < (eval (I * (ω : ℂ)) (b.map (algebraMap ℝ ℂ)) /
    eval (I * (ω : ℂ)) (a.map (algebraMap ℝ ℂ))).re

/-- Exact original target. This declaration asserts no proof of the proposition. -/
def RobustSPRStatement : Prop :=
  ∀ K : Box5, K.RobustlyHurwitz →
    ∃ b : ℝ[X], b.natDegree = 5 ∧ ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b

theorem quintic_natDegree (a : Poly5) : a.toPoly.natDegree = 5 := by
  unfold Poly5.toPoly
  compute_degree!

/-- 虚轴分解 a(iω)=E_a(ω²)+iω O_a(ω²) 的偶部。 -/
def evenPart (a : Poly5) (t : ℝ) : ℝ := a.a1 * t ^ 2 - a.a3 * t + a.a5

/-- 虚轴分解中乘在 iω 前的实二次多项式。 -/
def oddPart (a : Poly5) (t : ℝ) : ℝ := t ^ 2 - a.a2 * t + a.a4

def frequencyValue (a : Poly5) (ω : ℝ) : ℂ :=
  eval (I * (ω : ℂ)) (a.toPoly.map (algebraMap ℝ ℂ))

def pairing (a b : Poly5) (t : ℝ) : ℝ :=
  evenPart b t * evenPart a t + t * (oddPart b t * oddPart a t)

theorem frequencyValue_eq (a : Poly5) (ω : ℝ) :
    frequencyValue a ω = (evenPart a (ω ^ 2) : ℂ) +
      I * (ω : ℂ) * (oddPart a (ω ^ 2) : ℂ) := by
  simp only [frequencyValue, Poly5.toPoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    evenPart, oddPart, ofReal_add, ofReal_sub, ofReal_mul, ofReal_pow]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem frequencyValue_re (a : Poly5) (ω : ℝ) :
    (frequencyValue a ω).re = evenPart a (ω ^ 2) := by
  rw [frequencyValue_eq]
  simp

theorem frequencyValue_im (a : Poly5) (ω : ℝ) :
    (frequencyValue a ω).im = ω * oddPart a (ω ^ 2) := by
  rw [frequencyValue_eq]
  simp

theorem hurwitz_frequencyValue_ne_zero {a : Poly5} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    frequencyValue a ω ≠ 0 := by
  intro hz
  have hroot : (a.toPoly.map (algebraMap ℝ ℂ)).IsRoot (I * (ω : ℂ)) := hz
  have hh := ha _ hroot
  simp at hh

theorem real_ratio_eq (a b : Poly5) (ω : ℝ) :
    (frequencyValue b ω / frequencyValue a ω).re =
      pairing a b (ω ^ 2) / Complex.normSq (frequencyValue a ω) := by
  rw [Complex.div_re, frequencyValue_re, frequencyValue_re,
    frequencyValue_im, frequencyValue_im]
  unfold pairing
  rw [← add_div]
  congr 1
  ring

theorem positive_real_ratio_iff {a b : Poly5} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    0 < (frequencyValue b ω / frequencyValue a ω).re ↔ 0 < pairing a b (ω ^ 2) := by
  rw [real_ratio_eq]
  exact div_pos_iff_of_pos_right (Complex.normSq_pos.mpr (hurwitz_frequencyValue_ne_zero ha ω))

theorem frequencySPR_iff_pairing_pos {a b : Poly5} (ha : IsHurwitz a.toPoly) :
    FrequencySPR a.toPoly b.toPoly ↔ ∀ t : ℝ, 0 ≤ t → 0 < pairing a b t := by
  constructor
  · intro h t ht
    have hh := (positive_real_ratio_iff ha (Real.sqrt t)).mp (h (Real.sqrt t))
    simpa only [Real.sq_sqrt ht] using hh
  · intro h ω
    exact (positive_real_ratio_iff ha ω).mpr (h (ω ^ 2) (sq_nonneg ω))


inductive Corner where
  | D | A | B | C
  deriving DecidableEq, Fintype

def Box5.corner (K : Box5) : Corner → Poly5
  | .D => ⟨K.lower.a1, K.upper.a2, K.upper.a3, K.lower.a4, K.lower.a5⟩
  | .A => ⟨K.upper.a1, K.upper.a2, K.lower.a3, K.lower.a4, K.upper.a5⟩
  | .B => ⟨K.upper.a1, K.lower.a2, K.lower.a3, K.upper.a4, K.upper.a5⟩
  | .C => ⟨K.lower.a1, K.lower.a2, K.upper.a3, K.upper.a4, K.lower.a5⟩

theorem Box5.corner_mem (K : Box5) (c : Corner) : K.Contains (K.corner c) := by
  cases c <;> simp [Box5.Contains, Box5.corner, K.h1, K.h2, K.h3, K.h4, K.h5]

def Box5.evenLower (K : Box5) (t : ℝ) : ℝ :=
  K.lower.a1 * t ^ 2 - K.upper.a3 * t + K.lower.a5

def Box5.evenUpper (K : Box5) (t : ℝ) : ℝ :=
  K.upper.a1 * t ^ 2 - K.lower.a3 * t + K.upper.a5

def Box5.oddLower (K : Box5) (t : ℝ) : ℝ := t ^ 2 - K.upper.a2 * t + K.lower.a4

def Box5.oddUpper (K : Box5) (t : ℝ) : ℝ := t ^ 2 - K.lower.a2 * t + K.upper.a4

theorem Box5.component_bounds {K : Box5} {a : Poly5} (ha : K.Contains a)
    {t : ℝ} (ht : 0 ≤ t) :
    K.evenLower t ≤ evenPart a t ∧ evenPart a t ≤ K.evenUpper t ∧
      K.oddLower t ≤ oddPart a t ∧ oddPart a t ≤ K.oddUpper t := by
  rcases ha with ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u⟩
  unfold evenLower evenUpper oddLower oddUpper evenPart oddPart
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h1l) (sq_nonneg t),
      mul_nonneg (sub_nonneg.mpr h3u) ht, h5l]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h1u) (sq_nonneg t),
      mul_nonneg (sub_nonneg.mpr h3l) ht, h5u]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h2u) ht, h4l]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h2l) ht, h4u]

/-- At every nonnegative squared frequency, some fixed corner minimizes the pairing. -/
theorem Box5.exists_corner_le {K : Box5} {a : Poly5} (ha : K.Contains a)
    (b : Poly5) {t : ℝ} (ht : 0 ≤ t) :
    ∃ c : Corner, pairing (K.corner c) b t ≤ pairing a b t := by
  rcases K.component_bounds ha ht with ⟨hel, heu, hol, hou⟩
  by_cases he : 0 ≤ evenPart b t
  · have hE := mul_le_mul_of_nonneg_left hel he
    by_cases ho : 0 ≤ oddPart b t
    · have hO := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hol ho) ht
      refine ⟨.D, ?_⟩
      change evenPart b t * K.evenLower t + t * (oddPart b t * K.oddLower t) ≤
        evenPart b t * evenPart a t + t * (oddPart b t * oddPart a t) at ⊢
      exact add_le_add hE hO
    · have hO := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonpos_left hou (le_of_lt (lt_of_not_ge ho))) ht
      refine ⟨.C, ?_⟩
      change evenPart b t * K.evenLower t + t * (oddPart b t * K.oddUpper t) ≤
        evenPart b t * evenPart a t + t * (oddPart b t * oddPart a t) at ⊢
      exact add_le_add hE hO
  · have hE := mul_le_mul_of_nonpos_left heu (le_of_lt (lt_of_not_ge he))
    by_cases ho : 0 ≤ oddPart b t
    · have hO := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hol ho) ht
      refine ⟨.A, ?_⟩
      change evenPart b t * K.evenUpper t + t * (oddPart b t * K.oddLower t) ≤
        evenPart b t * evenPart a t + t * (oddPart b t * oddPart a t) at ⊢
      exact add_le_add hE hO
    · have hO := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonpos_left hou (le_of_lt (lt_of_not_ge ho))) ht
      refine ⟨.B, ?_⟩
      change evenPart b t * K.evenUpper t + t * (oddPart b t * K.oddUpper t) ≤
        evenPart b t * evenPart a t + t * (oddPart b t * oddPart a t) at ⊢
      exact add_le_add hE hO

/-- Four-corner positivity is proved directly, including degenerate boxes. -/
theorem Box5.pairing_pos_iff_corners (K : Box5) (b : Poly5) :
    (∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 < pairing a b t) ↔
      (∀ c : Corner, ∀ t : ℝ, 0 ≤ t → 0 < pairing (K.corner c) b t) := by
  constructor
  · intro h c
    exact h (K.corner c) (K.corner_mem c)
  · intro h a ha t ht
    obtain ⟨c, hc⟩ := K.exists_corner_le ha b ht
    exact lt_of_lt_of_le (h c t ht) hc

/-- The actual four-corner frequency equivalence, without any project synthesis axiom. -/
theorem Box5.frequencySPR_iff_corners (K : Box5) (hK : K.RobustlyHurwitz) (b : Poly5) :
    (∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b.toPoly) ↔
      (∀ c : Corner, FrequencySPR (K.corner c).toPoly b.toPoly) := by
  constructor
  · intro h c
    exact h _ (K.corner_mem c)
  · intro h a ha
    apply (frequencySPR_iff_pairing_pos (hK a ha)).mpr
    apply (K.pairing_pos_iff_corners b).mpr ?_ a ha
    intro c
    exact (frequencySPR_iff_pairing_pos (hK _ (K.corner_mem c))).mp (h c)

end
end SPR.N5.Direct
