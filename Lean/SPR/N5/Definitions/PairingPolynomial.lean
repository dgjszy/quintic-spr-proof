import SPR.N5.Definitions.General
import SPR.N5.Contacts.DegreeContacts
import SPR.N5.Contacts.OrderedContacts
import SPR.N5.Contacts.OriginContacts

/-! Polynomial interfaces connect local contact lemmas to actual interval corners.
## 与论文的对应

论文 §1–2：基本对象、精确主命题与虚轴分解。
将实函数配对转换为多项式，使系数、重数与次数引理可作用于原配对。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial

def numeratorEvenPoly (b : Vec6) : ℝ[X] := C (b 1) * X ^ 2 - C (b 3) * X + C (b 5)
def numeratorOddPoly (b : Vec6) : ℝ[X] := C (b 0) * X ^ 2 - C (b 2) * X + C (b 4)
def denominatorEvenPoly (a : Poly5) : ℝ[X] := C a.a1 * X ^ 2 - C a.a3 * X + C a.a5
def denominatorOddPoly (a : Poly5) : ℝ[X] := X ^ 2 - C a.a2 * X + C a.a4

def pairingPoly (a : Poly5) (b : Vec6) : ℝ[X] :=
  numeratorEvenPoly b * denominatorEvenPoly a + X * numeratorOddPoly b * denominatorOddPoly a

theorem pairingPoly_eval (a : Poly5) (b : Vec6) (t : ℝ) :
    (pairingPoly a b).eval t = generalPairing a b t := by
  simp only [pairingPoly, numeratorEvenPoly, numeratorOddPoly, denominatorEvenPoly,
    denominatorOddPoly, generalPairing, numeratorEven, numeratorOdd, evenPart, oddPart,
    eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem pairingPoly_expand (a : Poly5) (b : Vec6) :
    pairingPoly a b = C (b 0) * X ^ 5 +
      C (b 1*a.a1-b 0*a.a2-b 2) * X ^ 4 +
      C (b 0*a.a4+b 2*a.a2+b 4-b 1*a.a3-b 3*a.a1) * X ^ 3 +
      C (b 1*a.a5+b 3*a.a3+b 5*a.a1-b 2*a.a4-b 4*a.a2) * X ^ 2 +
      C (b 4*a.a4-b 3*a.a5-b 5*a.a3) * X + C (b 5*a.a5) := by
  simp only [pairingPoly, numeratorEvenPoly, numeratorOddPoly, denominatorEvenPoly,
    denominatorOddPoly, map_add, map_sub, map_mul]
  ring

theorem pairingPoly_coeff_five (a : Poly5) (b : Vec6) :
    (pairingPoly a b).coeff 5 = b 0 := by
  rw [pairingPoly_expand]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    OfNat.ofNat_ne_zero, ite_false, ite_true, add_zero, zero_add]

theorem pairingPoly_degree_le (a : Poly5) (b : Vec6) : (pairingPoly a b).natDegree ≤ 5 := by
  unfold pairingPoly numeratorEvenPoly numeratorOddPoly denominatorEvenPoly denominatorOddPoly
  compute_degree!

theorem pairingPoly_quartic_degree_le (a : Poly5) (b : Vec6) (hb : b 0 = 0) :
    (pairingPoly a b).natDegree ≤ 4 := by
  unfold pairingPoly numeratorEvenPoly numeratorOddPoly denominatorEvenPoly denominatorOddPoly
  rw [hb]
  simp only [map_zero, zero_mul, zero_sub]
  compute_degree!

theorem pairingPoly_no_three_contacts (a : Poly5) (b : Vec6)
    (hp : pairingPoly a b ≠ 0) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s u : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u)
    (hpr : generalPairing a b r = 0) (hps : generalPairing a b s = 0)
    (hpu : generalPairing a b u = 0) : False := by
  apply no_three_positive_contacts hp (pairingPoly_degree_le a b)
    (by simpa only [pairingPoly_eval] using hnonneg) hr hrs hsu
  · simpa only [pairingPoly_eval] using hpr
  · simpa only [pairingPoly_eval] using hps
  · simpa only [pairingPoly_eval] using hpu

theorem pairingPoly_constant (a : Poly5) (b : Vec6) :
    (pairingPoly a b).coeff 0 = b 5 * a.a5 := by
  rw [coeff_zero_eq_eval_zero, pairingPoly_eval]
  simp [generalPairing, numeratorEven, numeratorOdd, evenPart, oddPart]

theorem Box5.ab_constant_eq (K : Box5) (b : Vec6) :
    (pairingPoly (K.corner .A) b).coeff 0 = (pairingPoly (K.corner .B) b).coeff 0 := by
  simp only [pairingPoly_constant, corner]

theorem Box5.ab_difference (K : Box5) (b : Vec6) :
    pairingPoly (K.corner .B) b - pairingPoly (K.corner .A) b =
      X * numeratorOddPoly b * (C (K.upper.a2 - K.lower.a2) * X + C (K.upper.a4 - K.lower.a4)) := by
  simp only [pairingPoly, denominatorEvenPoly, denominatorOddPoly, corner, map_sub]
  ring

theorem odd_width_product_expand (b : Vec6) (d₂ d₄ : ℝ) :
    X * numeratorOddPoly b * (C d₂ * X + C d₄) =
      C (b 0*d₂) * X ^ 4 + C (b 0*d₄-b 2*d₂) * X ^ 3 +
      C (b 4*d₂-b 2*d₄) * X ^ 2 + C (b 4*d₄) * X := by
  simp only [numeratorOddPoly, map_add, map_sub, map_mul]
  ring

theorem Box5.ab_difference_coeff_four (K : Box5) (b : Vec6) :
    (pairingPoly (K.corner .B) b - pairingPoly (K.corner .A) b).coeff 4 =
      b 0 * (K.upper.a2 - K.lower.a2) := by
  rw [K.ab_difference, odd_width_product_expand]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, ite_false, ite_true,
    add_zero, zero_add]

/-- AB exclusion for the actual interval corners once their double-contact
factorizations have been established. Both b₀=0 and b₀>0 are allowed. -/
theorem Box5.ab_factorizations_impossible (K : Box5) (b : Vec6)
    {r s u v dA dB : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hc : 0 ≤ b 0) (hA : 0 ≤ dA) (hB : 0 ≤ dB) (hnz : 0 < b 0 + dA)
    (hPA : pairingPoly (K.corner .A) b = contactPoly (b 0) dA r s)
    (hPB : pairingPoly (K.corner .B) b = contactPoly (b 0) dB u v) : False := by
  apply ab_contact_polynomial_impossible hr hrs hsu huv hc hA hB hnz
    (sub_nonneg.mpr K.h2)
  · rw [← hPA, ← hPB]
    exact K.ab_constant_eq b
  · rw [← hPA, ← hPB]
    exact K.ab_difference_coeff_four b

/-- AB exclusion from actual nonnegative corner polynomials and their contacts.
No affine remainder factorization is assumed by this theorem. -/
theorem Box5.no_ordered_ab_contacts (K : Box5) (b : Vec6) (hb : 0 ≤ b 0)
    (hPA : pairingPoly (K.corner .A) b ≠ 0) (hPB : pairingPoly (K.corner .B) b ≠ 0)
    (hA : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing (K.corner .A) b t)
    (hB : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing (K.corner .B) b t)
    {r s u v : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (har : generalPairing (K.corner .A) b r = 0) (has : generalPairing (K.corner .A) b s = 0)
    (hbu : generalPairing (K.corner .B) b u = 0) (hbv : generalPairing (K.corner .B) b v = 0) :
    False := by
  obtain ⟨dA, hdA, hformA⟩ := two_contacts_factorization hPA (pairingPoly_degree_le _ b)
    (by simpa only [pairingPoly_eval] using hA) hr hrs
    (by simpa only [pairingPoly_eval] using har) (by simpa only [pairingPoly_eval] using has)
  obtain ⟨dB, hdB, hformB⟩ := two_contacts_factorization hPB (pairingPoly_degree_le _ b)
    (by simpa only [pairingPoly_eval] using hB) (hr.trans (hrs.trans hsu)) huv
    (by simpa only [pairingPoly_eval] using hbu) (by simpa only [pairingPoly_eval] using hbv)
  rw [pairingPoly_coeff_five] at hformA hformB
  have hnz : 0 < b 0 + dA := by
    by_contra h
    have hc0 : b 0 = 0 := by linarith
    have hd0 : dA = 0 := by linarith
    apply hPA
    simpa [contactPoly, hc0, hd0] using hformA
  exact K.ab_factorizations_impossible b hr hrs hsu huv hb hdA hdB hnz hformA hformB

theorem pairingPoly_origin_factorization (a : Poly5) (b : Vec6) (hb : b 5 = 0)
    (hp : pairingPoly a b ≠ 0) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hpr : generalPairing a b r = 0) (hps : generalPairing a b s = 0) :
    pairingPoly a b = X * (C (b 0) * (rootQuadratic r s) ^ 2) := by
  obtain ⟨d, _, hform⟩ := two_contacts_factorization hp (pairingPoly_degree_le a b)
    (by simpa only [pairingPoly_eval] using hnonneg) hr hrs
    (by simpa only [pairingPoly_eval] using hpr) (by simpa only [pairingPoly_eval] using hps)
  rw [pairingPoly_coeff_five] at hform
  have hzero := pairingPoly_constant a b
  rw [hb, zero_mul, hform, contactPoly_coeff_zero] at hzero
  have hd : d = 0 := (mul_eq_zero.mp hzero).resolve_right
    (ne_of_gt (sq_pos_of_pos (mul_pos hr (hr.trans hrs))))
  rw [hform, hd]
  simp only [contactPoly, rootQuadratic, map_zero, add_zero]
  ring

theorem Box5.bc_origin_difference (K : Box5) (b : Vec6) (hb : b 5 = 0) :
    pairingPoly (K.corner .C) b - pairingPoly (K.corner .B) b =
      X * (-(C (b 1) * X - C (b 3)) *
        (C (K.upper.a1 - K.lower.a1) * X ^ 2 +
          C (K.upper.a3 - K.lower.a3) * X + C (K.upper.a5 - K.lower.a5))) := by
  simp only [pairingPoly, numeratorEvenPoly, denominatorEvenPoly, denominatorOddPoly,
    corner, hb, map_zero, map_sub]
  ring

/-- The origin-zero BC rule now consumes actual nonnegative corner contacts.
The strict middle even-coefficient width is available in the full-dimensional critical box. -/
theorem Box5.no_origin_ordered_bc_contacts (K : Box5) (b : Vec6)
    (hb₀ : 0 < b 0) (hb₁ : 0 < b 1) (hb₅ : b 5 = 0)
    (hwidth : K.lower.a3 < K.upper.a3)
    (hPB : pairingPoly (K.corner .B) b ≠ 0) (hPC : pairingPoly (K.corner .C) b ≠ 0)
    (hB : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing (K.corner .B) b t)
    (hC : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing (K.corner .C) b t)
    {r s u v : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hbr : generalPairing (K.corner .B) b r = 0) (hbs : generalPairing (K.corner .B) b s = 0)
    (hcu : generalPairing (K.corner .C) b u = 0) (hcv : generalPairing (K.corner .C) b v = 0) :
    False := by
  have hformB := pairingPoly_origin_factorization _ b hb₅ hPB hB hr hrs hbr hbs
  have hformC := pairingPoly_origin_factorization _ b hb₅ hPC hC
    (hr.trans (hrs.trans hsu)) huv hcu hcv
  have hdiff := K.bc_origin_difference b hb₅
  rw [hformC, hformB, ← mul_sub, ← mul_sub] at hdiff
  have hcancel := mul_left_cancel₀ (X_ne_zero (R := ℝ)) hdiff
  exact origin_bc_polynomial_impossible hr hrs hsu huv hb₀ hb₁
    (sub_nonneg.mpr K.h1) (sub_pos.mpr hwidth) (sub_nonneg.mpr K.h5) hcancel

end
end SPR.N5.Direct
