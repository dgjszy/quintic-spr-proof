import SPR.N5.Contacts.DegreeContacts

/-! Coefficient obstructions for earlier contact modes, including quartic numerators.
## 与论文的对应

论文 §5：接触点重数、符号和极小顶点之间的联系。
计算二重接触因子的系数，证明 A 接触先于 B 接触时的系数矛盾。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial

def contactPoly (c d r s : ℝ) : ℝ[X] :=
  (C c * X + C d) * (X - C r) ^ 2 * (X - C s) ^ 2

theorem contactPoly_coeff_zero (c d r s : ℝ) :
    (contactPoly c d r s).coeff 0 = d * (r * s) ^ 2 := by
  rw [coeff_zero_eq_eval_zero]
  simp only [contactPoly, eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X,
    mul_zero, zero_add, zero_sub, neg_sq]
  ring

theorem contactPoly_expand (c d r s : ℝ) :
    contactPoly c d r s = C c * X ^ 5 + C (d - 2*c*(r+s)) * X ^ 4 +
      C (c*(r^2+4*r*s+s^2)-2*d*(r+s)) * X ^ 3 +
      C (d*(r^2+4*r*s+s^2)-2*c*r*s*(r+s)) * X ^ 2 +
      C (c*r^2*s^2-2*d*r*s*(r+s)) * X + C (d*r^2*s^2) := by
  simp only [contactPoly, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem contactPoly_coeff_four (c d r s : ℝ) :
    (contactPoly c d r s).coeff 4 = d - 2 * c * (r + s) := by
  rw [contactPoly_expand]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, OfNat.ofNat_ne_zero,
    ite_false, ite_true, add_zero, zero_add]

theorem contactPoly_coeff_five (c d r s : ℝ) :
    (contactPoly c d r s).coeff 5 = c := by
  rw [contactPoly_expand]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    OfNat.ofNat_ne_zero, ite_false, ite_true, add_zero, zero_add]

/-- Two distinct positive contacts produce an affine remainder. Its constant
is nonnegative, and the affine leading coefficient is the original fifth coefficient. -/
theorem two_contacts_factorization {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 5)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hpr : p.eval r = 0) (hps : p.eval s = 0) :
    ∃ d : ℝ, 0 ≤ d ∧ p = contactPoly (p.coeff 5) d r s := by
  have hcop : IsCoprime ((X - C r) ^ 2) ((X - C s) ^ 2) :=
    (distinct_linear_coprime (ne_of_lt hrs)).pow
  obtain ⟨q, hq⟩ := hcop.mul_dvd (nonnegative_contact_double_root hr hnonneg hpr)
    (nonnegative_contact_double_root (hr.trans hrs) hnonneg hps)
  have hq0 : q ≠ 0 := by intro hz; simp [hz] at hq; exact hp hq
  have hbase := ((monic_X_sub_C r).pow 2).mul ((monic_X_sub_C s).pow 2)
  have hbaseDeg : (((X - C r) ^ 2 * (X - C s) ^ 2) : ℝ[X]).natDegree = 4 := by
    rw [((monic_X_sub_C r).pow 2).natDegree_mul ((monic_X_sub_C s).pow 2),
      (monic_X_sub_C r).natDegree_pow, (monic_X_sub_C s).natDegree_pow]
    simp
  have hqdeg : q.natDegree ≤ 1 := by
    rw [hq, natDegree_mul hbase.ne_zero hq0, hbaseDeg] at hdeg
    omega
  obtain ⟨c, d, hform⟩ := exists_eq_X_add_C_of_natDegree_le_one hqdeg
  have hpoly : p = contactPoly c d r s := by
    rw [hq, hform]
    unfold contactPoly
    ring
  have hdc : 0 ≤ d := by
    have h0 := hnonneg 0 le_rfl
    rw [← coeff_zero_eq_eval_zero, hpoly, contactPoly_coeff_zero] at h0
    exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (mul_pos hr (hr.trans hrs)))).mp h0
  refine ⟨d, hdc, ?_⟩
  have hc : p.coeff 5 = c := by rw [hpoly, contactPoly_coeff_five]
  simpa only [hc] using hpoly

theorem ordered_contact_constant_bounds {r s u v dA dB : ℝ}
    (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hA : 0 ≤ dA) (hB : 0 ≤ dB)
    (hconstant : dA * (r * s) ^ 2 = dB * (u * v) ^ 2) :
    dB ≤ dA ∧ (0 < dA → dB < dA) := by
  have hs : 0 < s := hr.trans hrs
  have hu : 0 < u := hs.trans hsu
  have hprod : r * s < u * v :=
    mul_lt_mul (hrs.trans hsu) (hsu.trans huv).le hs hu.le
  have hp0 : 0 < r * s := mul_pos hr hs
  have hsq : (r * s) ^ 2 < (u * v) ^ 2 := by nlinarith
  have hsq0 : 0 < (u * v) ^ 2 := sq_pos_of_pos (mul_pos hu (hu.trans huv))
  constructor
  · by_contra h
    have hh : dA < dB := lt_of_not_ge h
    have h1 := mul_lt_mul_of_pos_right hh hsq0
    have h2 := mul_le_mul_of_nonneg_left hsq.le hA
    nlinarith
  · intro hpos
    by_contra h
    have hh : dA ≤ dB := le_of_not_gt h
    have h1 := mul_le_mul_of_nonneg_right hh hsq0.le
    have h2 := mul_lt_mul_of_pos_left hsq hpos
    nlinarith

/-- The equal constant terms force the wrong sign of the fourth coefficient.
`c + dA > 0` covers both the degree-five and the nonzero degree-four case. -/
theorem ab_coefficient_impossible {r s u v c dA dB delta : ℝ}
    (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hc : 0 ≤ c) (hA : 0 ≤ dA) (hB : 0 ≤ dB) (hnz : 0 < c + dA)
    (hdelta : 0 ≤ delta)
    (hconstant : dA * (r * s) ^ 2 = dB * (u * v) ^ 2)
    (hfour : dB - dA - 2 * c * (u + v - r - s) = c * delta) : False := by
  obtain ⟨hBA, hBAstrict⟩ := ordered_contact_constant_bounds hr hrs hsu huv hA hB hconstant
  have hgap : 0 < u + v - r - s := by linarith
  have hright : 0 ≤ c * delta := mul_nonneg hc hdelta
  by_cases hc0 : c = 0
  · have hd : 0 < dA := by simpa only [hc0, zero_add] using hnz
    have hlt := hBAstrict hd
    simp only [hc0, mul_zero, zero_mul, sub_zero] at hfour
    linarith
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hleft : 0 < 2 * c * (u + v - r - s) :=
      mul_pos (mul_pos (by norm_num) hcpos) hgap
    linarith

/-- Polynomial-facing AB obstruction: equality of constants and the fourth
coefficient identity are the only common-corner data consumed by the proof. -/
theorem ab_contact_polynomial_impossible {r s u v c dA dB delta : ℝ}
    (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hc : 0 ≤ c) (hA : 0 ≤ dA) (hB : 0 ≤ dB) (hnz : 0 < c + dA)
    (hdelta : 0 ≤ delta)
    (hconstant : (contactPoly c dA r s).coeff 0 = (contactPoly c dB u v).coeff 0)
    (hfour : (contactPoly c dB u v - contactPoly c dA r s).coeff 4 = c * delta) :
    False := by
  rw [contactPoly_coeff_zero, contactPoly_coeff_zero] at hconstant
  rw [coeff_sub, contactPoly_coeff_four, contactPoly_coeff_four] at hfour
  apply ab_coefficient_impossible hr hrs hsu huv hc hA hB hnz hdelta hconstant
  nlinarith only [hfour]

end
end SPR.N5.Direct
