import SPR.N5.Contacts.PairingNonzero

/-! Coefficient positivity from Hurwitz stability, via the library Gauss-Lucas
theorem. All derivative degree hypotheses are explicit.
## 与论文的对应

论文 §2：Hurwitz 稳定性、零点交错及统一分母零点区间。
由稳定性证明系数正性，供分母交错和原点处取值使用。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Set

theorem hurwitz_derivative {p : ℝ[X]} (hp : IsHurwitz p) (hdeg : 0 < p.natDegree) :
    IsHurwitz p.derivative := by
  let P := p.map (algebraMap ℝ ℂ)
  have hPdeg : 0 < P.natDegree := by simpa [P] using hdeg
  have hPdne : P.derivative ≠ 0 := by
    have hd := degree_derivative_eq P hPdeg
    intro he
    simp [he] at hd
  have hconv : Convex ℝ {z : ℂ | z.re < 0} :=
    (convex_Iio (0 : ℝ)).linear_preimage Complex.reLm
  have hroots : P.rootSet ℂ ⊆ {z : ℂ | z.re < 0} := by
    intro z hz
    exact hp z (by simpa [P, coe_aeval_eq_eval] using (mem_rootSet.mp hz).2)
  intro z hz
  have hm : z ∈ P.derivative.rootSet ℂ := by
    apply mem_rootSet.mpr
    refine ⟨hPdne, ?_⟩
    simpa [P, derivative_map, coe_aeval_eq_eval] using hz
  exact (convexHull_min hroots hconv)
    (P.rootSet_derivative_subset_convexHull_rootSet
      (natDegree_pos_iff_degree_pos.mp hPdeg) hm)

theorem derivative_natDegree_exact {p : ℝ[X]} (hdeg : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 :=
  natDegree_eq_of_degree_eq_some (degree_derivative_eq p hdeg)

theorem derivative_leadingCoeff_pos {p : ℝ[X]} (hlc : 0 < p.leadingCoeff)
    (hdeg : 0 < p.natDegree) : 0 < p.derivative.leadingCoeff := by
  rw [← coeff_natDegree, derivative_natDegree_exact hdeg, coeff_derivative,
    Nat.sub_add_cancel (by omega : 1 ≤ p.natDegree), coeff_natDegree]
  exact mul_pos hlc (by positivity)

theorem hurwitz_coeff_pos {p : ℝ[X]} (hp : IsHurwitz p) (hlc : 0 < p.leadingCoeff)
    (n : ℕ) (hn : n ≤ p.natDegree) : 0 < p.coeff n := by
  induction n generalizing p with
  | zero =>
    rw [coeff_zero_eq_eval_zero]
    exact hurwitz_eval_pos hp hlc.le le_rfl
  | succ n ih =>
    have hdeg : 0 < p.natDegree := by omega
    have hn' : n ≤ p.derivative.natDegree := by
      rw [derivative_natDegree_exact hdeg]
      omega
    have h := ih (hurwitz_derivative hp hdeg) (derivative_leadingCoeff_pos hlc hdeg) hn'
    rw [coeff_derivative] at h
    exact (mul_pos_iff_of_pos_right (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mp h

theorem quintic_coefficients_pos {a : Poly5} (ha : IsHurwitz a.toPoly) :
    0 < a.a1 ∧ 0 < a.a2 ∧ 0 < a.a3 ∧ 0 < a.a4 ∧ 0 < a.a5 := by
  have hlc : 0 < a.toPoly.leadingCoeff := by rw [(quintic_monic a).leadingCoeff]; norm_num
  have h (n : ℕ) (hn : n ≤ 5) : 0 < a.toPoly.coeff n :=
    hurwitz_coeff_pos ha hlc n (by rwa [quintic_natDegree])
  have h1 := h 4 (by omega)
  have h2 := h 3 (by omega)
  have h3 := h 2 (by omega)
  have h4 := h 1 (by omega)
  have h5 := h 0 (by omega)
  norm_num [Poly5.toPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end
end SPR.N5.Direct
