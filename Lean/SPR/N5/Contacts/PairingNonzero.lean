import SPR.N5.Definitions.PairingPolynomial
import SPR.N5.Critical.CriticalMoments

/-! Hurwitz stability rules out an identically zero pairing with a nonzero
numerator of degree at most five. No positive-real structure theorem is assumed.
## 与论文的对应

论文 §5：接触点重数、符号和极小顶点之间的联系。
用 Hurwitz 稳定性与反射多项式互素性证明非零分子的配对不恒为零。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial

def reflectPoly (p : ℝ[X]) : ℝ[X] := p.comp (-X)

theorem aeval_reflectPoly (p : ℝ[X]) (z : ℂ) :
    aeval z (reflectPoly p) = aeval (-z) p := by
  simp [reflectPoly, aeval_def, eval₂_comp]

/-- A Hurwitz polynomial and its reflection have no common complex root. -/
theorem hurwitz_isCoprime_reflection {p : ℝ[X]} (hp : IsHurwitz p) :
    IsCoprime p (reflectPoly p) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ p (reflectPoly p)).mpr
  intro z
  by_cases hz : aeval z p = 0
  · right
    intro hr
    rw [aeval_reflectPoly] at hr
    have hleft : z.re < 0 := hp z (by simpa [aeval_def, eval_map] using hz)
    have hright : (-z).re < 0 := hp (-z) (by simpa [aeval_def, eval_map] using hr)
    simp only [Complex.neg_re] at hright
    linarith
  · exact Or.inl hz

theorem pairing_reflection_identity (a : Poly5) (b : Vec6) :
    numeratorPoly b * reflectPoly a.toPoly + reflectPoly (numeratorPoly b) * a.toPoly =
      C 2 * (pairingPoly a b).comp (-X ^ 2) := by
  simp only [reflectPoly, numeratorPoly, Poly5.toPoly, pairingPoly, numeratorEvenPoly,
    numeratorOddPoly, denominatorEvenPoly, denominatorOddPoly, add_comp, sub_comp,
    mul_comp, pow_comp, C_comp, X_comp, map_ofNat]
  ring

theorem quintic_monic (a : Poly5) : a.toPoly.Monic := by
  unfold Poly5.toPoly
  monicity!

theorem numeratorPoly_degree_le (b : Vec6) : (numeratorPoly b).natDegree ≤ 5 := by
  unfold numeratorPoly
  compute_degree!

theorem pairingPoly_ne_zero_of_hurwitz (a : Poly5) (ha : IsHurwitz a.toPoly)
    (b : Vec6) (hb : b ≠ 0) : pairingPoly a b ≠ 0 := by
  intro hz
  have hid := pairing_reflection_identity a b
  rw [hz, zero_comp, mul_zero] at hid
  have hdvd : a.toPoly ∣ numeratorPoly b * reflectPoly a.toPoly := by
    rw [eq_neg_of_add_eq_zero_left hid]
    exact dvd_neg.mpr (dvd_mul_left _ _)
  have hdiv := (hurwitz_isCoprime_reflection ha).dvd_of_dvd_mul_right hdvd
  have hdeg : (numeratorPoly b).natDegree ≤ a.toPoly.natDegree := by
    rw [quintic_natDegree]
    exact numeratorPoly_degree_le b
  have hform := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    (quintic_monic a) hdiv hdeg
  have hb0 : b 0 = 0 := by
    have he := congrArg (fun p : ℝ[X] => p.coeff 5) hz
    simpa only [pairingPoly_coeff_five, coeff_zero] using he
  have hlc : (numeratorPoly b).leadingCoeff = 0 := by
    have he := congrArg (fun p : ℝ[X] => p.coeff 5) hform
    simpa only [coeff_mul_C, ← quintic_natDegree a, coeff_natDegree,
      (quintic_monic a).leadingCoeff, one_mul] using he.symm.trans
        ((numeratorPoly_coeff_descending b 0).trans hb0)
  exact numeratorPoly_ne_zero hb (leadingCoeff_eq_zero.mp hlc)

theorem hurwitz_real_root_neg {p : ℝ[X]} (hp : IsHurwitz p) {x : ℝ}
    (hx : p.IsRoot x) : x < 0 := by
  exact hp (x : ℂ) (hx.map (f := algebraMap ℝ ℂ))

theorem hurwitz_eval_pos {p : ℝ[X]} (hp : IsHurwitz p)
    (hlc : 0 ≤ p.leadingCoeff) {x : ℝ} (hx : 0 ≤ x) : 0 < p.eval x := by
  exact zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun y hy => (hurwitz_real_root_neg hp hy).trans_le hx) hlc

theorem quintic_constant_pos {a : Poly5} (ha : IsHurwitz a.toPoly) : 0 < a.a5 := by
  have hlc : 0 ≤ a.toPoly.leadingCoeff := by rw [(quintic_monic a).leadingCoeff]; norm_num
  simpa [Poly5.toPoly] using hurwitz_eval_pos ha hlc (x := 0) le_rfl

theorem weak_numerator_constant_nonneg {a : Poly5} (ha : IsHurwitz a.toPoly)
    {b : Vec6} (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) : 0 ≤ b 5 := by
  have h : 0 ≤ b 5 * a.a5 := by
    simpa [generalPairing, numeratorEven, numeratorOdd, evenPart, oddPart] using hw 0 le_rfl
  exact (mul_nonneg_iff_of_pos_right (quintic_constant_pos ha)).mp h

theorem origin_contact_iff_constant_zero {a : Poly5} (ha : IsHurwitz a.toPoly)
    (b : Vec6) : generalPairing a b 0 = 0 ↔ b 5 = 0 := by
  simp [generalPairing, numeratorEven, numeratorOdd, evenPart, oddPart,
    ne_of_gt (quintic_constant_pos ha)]

theorem denominator_even_odd_decomposition (a : Poly5) (z : ℂ) :
    aeval z a.toPoly = aeval (-(z ^ 2)) (denominatorEvenPoly a) +
      z * aeval (-(z ^ 2)) (denominatorOddPoly a) := by
  simp only [Poly5.toPoly, denominatorEvenPoly, denominatorOddPoly, map_add, map_sub,
    map_mul, map_pow, aeval_X, aeval_C]
  ring

theorem denominator_even_odd_isCoprime {a : Poly5} (ha : IsHurwitz a.toPoly) :
    IsCoprime (denominatorEvenPoly a) (denominatorOddPoly a) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).mpr
  intro t
  by_cases he : aeval t (denominatorEvenPoly a) = 0
  · right
    intro ho
    obtain ⟨z, hzsq⟩ := IsAlgClosed.exists_pow_nat_eq (-t) (n := 2) (by decide)
    have hzt : -(z ^ 2) = t := by rw [hzsq, neg_neg]
    have hz : aeval z a.toPoly = 0 := by
      rw [denominator_even_odd_decomposition, hzt, he, ho]; ring
    have hnz : aeval (-z) a.toPoly = 0 := by
      rw [denominator_even_odd_decomposition, neg_sq, hzt, he, ho]; ring
    have hleft := ha z (by simpa [aeval_def, eval_map] using hz)
    have hright := ha (-z) (by simpa [aeval_def, eval_map] using hnz)
    simp only [Complex.neg_re] at hright
    linarith
  · exact Or.inl he

theorem denominator_even_Xodd_isCoprime {a : Poly5} (ha : IsHurwitz a.toPoly) :
    IsCoprime (denominatorEvenPoly a) (X * denominatorOddPoly a) := by
  apply IsCoprime.mul_right _ (denominator_even_odd_isCoprime ha)
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).mpr
  intro z
  by_cases hz : z = 0
  · left
    subst z
    simpa [denominatorEvenPoly] using
      (show (a.a5 : ℂ) ≠ 0 by exact_mod_cast ne_of_gt (quintic_constant_pos ha))
  · right
    simpa using hz

end
end SPR.N5.Direct
