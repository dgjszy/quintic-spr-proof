import Mathlib

/-! Interior nonnegative contacts are double roots; degree excludes excess contacts.
## 与论文的对应

论文 §5：接触点重数、符号和极小顶点之间的联系。
半轴内的非负多项式零点是至少二重根；用次数上界排除过多接触。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Set

theorem nonnegative_contact_derivative {p : ℝ[X]} {r : ℝ} (hr : 0 < r)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) (hzero : p.eval r = 0) :
    p.derivative.eval r = 0 := by
  have hmin : IsMinOn (fun t => p.eval t) (Ioi (0 : ℝ)) r := by
    intro t ht
    simpa only [hzero] using hnonneg t (le_of_lt ht)
  exact (hmin.isLocalMin (Ioi_mem_nhds hr)).hasDerivAt_eq_zero (p.hasDerivAt r)

theorem double_root_dvd_of_eval_derivative {p : ℝ[X]} {r : ℝ}
    (hzero : p.eval r = 0) (hderiv : p.derivative.eval r = 0) :
    (X - C r) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot).mpr hzero
  have hqr : q.eval r = 0 := by
    rw [hq, derivative_mul] at hderiv
    simpa using hderiv
  obtain ⟨v, hv⟩ := (dvd_iff_isRoot).mpr hqr
  refine ⟨v, ?_⟩
  rw [hq, hv]
  ring

theorem nonnegative_contact_double_root {p : ℝ[X]} {r : ℝ} (hr : 0 < r)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) (hzero : p.eval r = 0) :
    (X - C r) ^ 2 ∣ p :=
  double_root_dvd_of_eval_derivative hzero (nonnegative_contact_derivative hr hnonneg hzero)

theorem distinct_linear_coprime {r s : ℝ} (hrs : r ≠ s) :
    IsCoprime (X - C r) (X - C s) :=
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hrs).isUnit

theorem three_double_roots_degree_ge {p : ℝ[X]} (hp : p ≠ 0) {r s u : ℝ}
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (hr : (X - C r) ^ 2 ∣ p) (hs : (X - C s) ^ 2 ∣ p) (hu : (X - C u) ^ 2 ∣ p) :
    6 ≤ p.natDegree := by
  have hab : IsCoprime ((X - C r) ^ 2) ((X - C s) ^ 2) := (distinct_linear_coprime hrs).pow
  have hac : IsCoprime ((X - C r) ^ 2) ((X - C u) ^ 2) := (distinct_linear_coprime hru).pow
  have hbc : IsCoprime ((X - C s) ^ 2) ((X - C u) ^ 2) := (distinct_linear_coprime hsu).pow
  have hdvd := (hac.mul_left hbc).mul_dvd (hab.mul_dvd hr hs) hu
  have hdeg := natDegree_le_of_dvd hdvd hp
  have mr := (monic_X_sub_C r).pow 2
  have ms := (monic_X_sub_C s).pow 2
  have mu := (monic_X_sub_C u).pow 2
  simpa only [(mr.mul ms).natDegree_mul mu, mr.natDegree_mul ms,
    (monic_X_sub_C r).natDegree_pow, (monic_X_sub_C s).natDegree_pow,
    (monic_X_sub_C u).natDegree_pow, natDegree_X_sub_C, mul_one] using hdeg

theorem no_three_positive_contacts {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 5)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t)
    {r s u : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u)
    (hpr : p.eval r = 0) (hps : p.eval s = 0) (hpu : p.eval u = 0) : False := by
  have h6 := three_double_roots_degree_ge hp (ne_of_lt hrs) (ne_of_lt (hrs.trans hsu))
    (ne_of_lt hsu) (nonnegative_contact_double_root hr hnonneg hpr)
    (nonnegative_contact_double_root (hr.trans hrs) hnonneg hps)
    (nonnegative_contact_double_root (hr.trans (hrs.trans hsu)) hnonneg hpu)
  omega

theorem zero_and_two_double_roots_degree_ge {p : ℝ[X]} (hp : p ≠ 0) {r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s)
    (hzero : p.eval 0 = 0) (hpr : (X - C r) ^ 2 ∣ p) (hps : (X - C s) ^ 2 ∣ p) :
    5 ≤ p.natDegree := by
  have hab : IsCoprime ((X - C r) ^ 2) ((X - C s) ^ 2) := (distinct_linear_coprime hrs).pow
  have h0r : IsCoprime (X - C (0 : ℝ)) ((X - C r) ^ 2) :=
    (distinct_linear_coprime (Ne.symm hr)).pow_right
  have h0s : IsCoprime (X - C (0 : ℝ)) ((X - C s) ^ 2) :=
    (distinct_linear_coprime (Ne.symm hs)).pow_right
  have hdvd := (h0r.mul_right h0s).mul_dvd ((dvd_iff_isRoot).mpr hzero)
    (hab.mul_dvd hpr hps)
  have hdeg := natDegree_le_of_dvd hdvd hp
  have mr := (monic_X_sub_C r).pow 2
  have ms := (monic_X_sub_C s).pow 2
  simpa only [(monic_X_sub_C (0 : ℝ)).natDegree_mul (mr.mul ms), mr.natDegree_mul ms,
    (monic_X_sub_C r).natDegree_pow, (monic_X_sub_C s).natDegree_pow,
    natDegree_X_sub_C, mul_one] using hdeg

theorem no_origin_and_two_quartic_contacts {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 4)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) (hzero : p.eval 0 = 0)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hpr : p.eval r = 0) (hps : p.eval s = 0) : False := by
  have h5 := zero_and_two_double_roots_degree_ge hp (ne_of_gt hr) (ne_of_gt (hr.trans hrs))
    (ne_of_lt hrs) hzero (nonnegative_contact_double_root hr hnonneg hpr)
    (nonnegative_contact_double_root (hr.trans hrs) hnonneg hps)
  omega

end
end SPR.N5.Direct
