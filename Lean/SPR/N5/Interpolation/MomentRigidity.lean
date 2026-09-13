import SPR.N5.Interpolation.MomentInterpolation

/-!
# MomentRigidity

论文 §4.3：消失矩、插值恒等式及支持点个数。
将节点接触等式提升为多项式恒等式，再由互素性提取公共多项式倍数。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial Finset

theorem degree_mul_residuePoly_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) (p : ℝ[X]) {k : ℕ}
    (hp : p.degree ≤ k) (hm : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0) :
    (p * residuePoly s t z).degree < (s.card : WithBot ℕ) := by
  rw [degree_mul, add_comm]
  exact (_root_.add_le_add le_rfl hp).trans_lt (degree_residuePoly_moments s t z k hm)

/-- The contact equations and the first two moments already force a polynomial
identity when both multiplying polynomials have degree at most two. -/
theorem contact_residue_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ) (ht : Set.InjOn t s)
    (E O : ℝ[X]) (hE : E.degree ≤ 2) (hO : O.degree ≤ 2)
    (hz : ∀ j < 2, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < 2, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i + O.eval (t i) * y i = 0) :
    E * residuePoly s t z + O * residuePoly s t y = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero s ht
  · exact (degree_add_le _ _).trans_lt (max_lt_iff.mpr
      ⟨degree_mul_residuePoly_lt s t z E hE hz,
        degree_mul_residuePoly_lt s t y O hO hy⟩)
  · intro i hi
    simp only [eval_add, eval_mul, eval_residuePoly ht hi]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hc i hi, zero_mul]

/-- Coprimality upgrades the contact identity to a common polynomial multiplier. -/
theorem coprime_contact_multiplier {E O U V : ℝ[X]}
    (hcop : IsCoprime E O) (hE : E ≠ 0) (h : E * U + O * V = 0) :
    ∃ Q : ℝ[X], V = E * Q ∧ U = -(O * Q) := by
  have hd : E ∣ O * V := by
    rw [eq_neg_of_add_eq_zero_right h]
    exact dvd_neg.mpr (dvd_mul_right E U)
  obtain ⟨Q,hQ⟩ := hcop.dvd_of_dvd_mul_left hd
  refine ⟨Q,hQ,?_⟩
  apply mul_left_cancel₀ hE
  rw [hQ] at h
  calc
    E * U = -(O * (E * Q)) := eq_neg_of_add_eq_zero_left h
    _ = E * -(O * Q) := by ring

/-- A nonzero even residue requires at least four distinct finite nodes. -/
theorem four_le_of_even_moments {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {t z : ι → ℝ} (ht : Set.InjOn t s)
    (hz : ∃ i ∈ s, z i ≠ 0)
    (hm : ∀ j < 3, (∑ i ∈ s, (t i)^j * z i) = 0) : 4 ≤ s.card := by
  by_contra h
  obtain ⟨i,hi,hzi⟩ := hz
  exact hzi (weights_zero_of_moments ht (by omega : s.card ≤ 3) hm i hi)

end
end SPR.N5.Direct
