import SPR.N5.Algebra.WeakCoprime

/-!
# RootBands

论文 §2：Hurwitz 稳定性、零点交错及统一分母零点区间。
构造全族适用的四个分母零点区间，并证明八端点的严格次序。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial

theorem ordered_factor_roots_unique {p : ℝ → ℝ} {a d r s u v : ℝ}
    (ha : a ≠ 0) (hd : d ≠ 0) (hrs : r < s) (huv : u < v)
    (hp : ∀ t, p t = a * ((t-r)*(t-s))) (hq : ∀ t, p t = d * ((t-u)*(t-v))) :
    r = u ∧ s = v := by
  have hr : r = u ∨ r = v := by
    have he : d * ((r-u)*(r-v)) = 0 := by rw [← hq,hp]; ring
    simpa [hd,mul_eq_zero,sub_eq_zero] using he
  have hs : s = u ∨ s = v := by
    have he : d * ((s-u)*(s-v)) = 0 := by rw [← hq,hp]; ring
    simpa [hd,mul_eq_zero,sub_eq_zero] using he
  rcases hr with hr | hr <;> rcases hs with hs | hs <;> constructor <;> linarith

theorem quadratic_negative_between {a r s t : ℝ} (ha : 0 < a) (hrs : r < s)
    (h : a * ((t-r)*(t-s)) < 0) : r < t ∧ t < s := by
  have hp : (t-r)*(t-s) < 0 := by
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg ha.le (le_of_not_gt hn))) h
  rcases mul_neg_iff.mp hp with h | h
  · exact ⟨sub_pos.mp h.1,sub_neg.mp h.2⟩
  · exfalso
    have htr := sub_neg.mp h.1
    have hst := sub_pos.mp h.2
    linarith

theorem Box5.even_bounds_strict (K : Box5) (hw : K.FullWidth) {t : ℝ} (ht : 0 ≤ t) :
    K.evenLower t < K.evenUpper t := by
  rcases hw with ⟨h1,h2,h3,h4,h5⟩
  unfold evenLower evenUpper
  nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (sq_nonneg t),
    mul_nonneg (sub_nonneg.mpr h3.le) ht]

theorem Box5.odd_bounds_strict (K : Box5) (hw : K.FullWidth) {t : ℝ} (ht : 0 ≤ t) :
    K.oddLower t < K.oddUpper t := by
  rcases hw with ⟨h1,h2,h3,h4,h5⟩
  unfold oddLower oddUpper
  nlinarith [mul_nonneg (sub_nonneg.mpr h2.le) ht]

/-- Eight strictly ordered endpoints of the four global denominator root bands. -/
structure RootBands (K : Box5) where
  eL : ℝ
  eU : ℝ
  oL : ℝ
  oU : ℝ
  fL : ℝ
  fU : ℝ
  pL : ℝ
  pU : ℝ
  ordered : 0 < eL ∧ eL < eU ∧ eU < oL ∧ oL < oU ∧
    oU < fL ∧ fL < fU ∧ fU < pL ∧ pL < pU
  even_lower : ∀ t, K.evenLower t = K.lower.a1 * ((t-eL)*(t-fU))
  even_upper : ∀ t, K.evenUpper t = K.upper.a1 * ((t-eU)*(t-fL))
  odd_lower : ∀ t, K.oddLower t = (t-oL)*(t-pU)
  odd_upper : ∀ t, K.oddUpper t = (t-oU)*(t-pL)

theorem Box5.rootBands (K : Box5) (hK : K.RobustlyHurwitz) (hw : K.FullWidth) :
    Nonempty (RootBands K) := by
  obtain ⟨A⟩ := denominator_interlacing (hK _ (K.corner_mem .A))
  obtain ⟨B⟩ := denominator_interlacing (hK _ (K.corner_mem .B))
  obtain ⟨C⟩ := denominator_interlacing (hK _ (K.corner_mem .C))
  have ha : 0 < K.upper.a1 := (quintic_coefficients_pos (hK _ (K.corner_mem .A))).1
  have hc : 0 < K.lower.a1 := (quintic_coefficients_pos (hK _ (K.corner_mem .C))).1
  have hEA (t : ℝ) : K.evenUpper t = K.upper.a1 * ((t-A.e₁)*(t-A.e₂)) := A.even_eval t
  have hEC (t : ℝ) : K.evenLower t = K.lower.a1 * ((t-C.e₁)*(t-C.e₂)) := C.even_eval t
  have hOA (t : ℝ) : K.oddLower t = (t-A.o₁)*(t-A.o₂) := A.odd_eval t
  have hOC (t : ℝ) : K.oddUpper t = (t-C.o₁)*(t-C.o₂) := C.odd_eval t
  have hEB (t : ℝ) : K.evenUpper t = K.upper.a1 * ((t-B.e₁)*(t-B.e₂)) := B.even_eval t
  have hOB (t : ℝ) : K.oddUpper t = 1 * ((t-B.o₁)*(t-B.o₂)) := by simpa using B.odd_eval t
  have heq := ordered_factor_roots_unique (ne_of_gt ha) (ne_of_gt ha)
    (A.e₁_lt_o₁.trans A.o₁_lt_e₂) (B.e₁_lt_o₁.trans B.o₁_lt_e₂) hEA hEB
  have hoq := ordered_factor_roots_unique (a := 1) one_ne_zero one_ne_zero
    (C.o₁_lt_e₂.trans C.e₂_lt_o₂) (B.o₁_lt_e₂.trans B.e₂_lt_o₂)
    (fun t => by simpa using hOC t) hOB
  have he1 : C.e₁ < A.e₁ ∧ A.e₁ < C.e₂ := by
    apply quadratic_negative_between hc (C.e₁_lt_o₁.trans C.o₁_lt_e₂)
    have hh := K.even_bounds_strict hw A.e₁_pos.le
    rw [hEA,hEC] at hh
    nlinarith
  have he2 : C.e₁ < A.e₂ ∧ A.e₂ < C.e₂ := by
    apply quadratic_negative_between hc (C.e₁_lt_o₁.trans C.o₁_lt_e₂)
    have hh := K.even_bounds_strict hw (A.e₁_pos.trans (A.e₁_lt_o₁.trans A.o₁_lt_e₂)).le
    rw [hEA,hEC] at hh
    nlinarith
  have ho1 : A.o₁ < C.o₁ ∧ C.o₁ < A.o₂ := by
    apply quadratic_negative_between (a := 1) zero_lt_one (A.o₁_lt_e₂.trans A.e₂_lt_o₂)
    have hh := K.odd_bounds_strict hw (C.e₁_pos.trans C.e₁_lt_o₁).le
    rw [hOA,hOC] at hh
    nlinarith
  have ho2 : A.o₁ < C.o₂ ∧ C.o₂ < A.o₂ := by
    apply quadratic_negative_between (a := 1) zero_lt_one (A.o₁_lt_e₂.trans A.e₂_lt_o₂)
    have hh := K.odd_bounds_strict hw
      (C.e₁_pos.trans (C.e₁_lt_o₁.trans (C.o₁_lt_e₂.trans C.e₂_lt_o₂))).le
    rw [hOA,hOC] at hh
    nlinarith
  have hmid : C.o₁ < A.e₂ := by rw [hoq.1,heq.2]; exact B.o₁_lt_e₂
  exact ⟨⟨C.e₁,A.e₁,A.o₁,C.o₁,A.e₂,C.e₂,C.o₂,A.o₂,
    ⟨C.e₁_pos,he1.1,A.e₁_lt_o₁,ho1.1,hmid,he2.2,C.e₂_lt_o₂,ho2.2⟩,
    hEC,hEA,hOA,hOC⟩⟩

end
end SPR.N5.Direct
