import Mathlib

/-!
# MomentInterpolation

论文 §4.3：消失矩、插值恒等式及支持点个数。
定义按权重构造的插值多项式，并证明消失 k 阶矩导致次数下降。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial Finset

/-- The polynomial whose residues at the distinct nodes are the prescribed weights. -/
def residuePoly {ι : Type*} [DecidableEq ι] (s : Finset ι) (t z : ι → ℝ) : ℝ[X] :=
  ∑ i ∈ s, C (z i) * Lagrange.nodal (s.erase i) t

theorem eval_residuePoly {ι : Type*} [DecidableEq ι] {s : Finset ι} {t z : ι → ℝ}
    (ht : Set.InjOn t s) {i : ι} (hi : i ∈ s) :
    (residuePoly s t z).eval (t i) = z i * ∏ j ∈ s.erase i, (t i - t j) := by
  simp only [residuePoly, eval_finsetSum, eval_mul, eval_C]
  rw [sum_eq_single i]
  · rw [Lagrange.eval_nodal]
  · intro j hj hji
    rw [Lagrange.eval_nodal_at_node (mem_erase.mpr ⟨hji.symm,hi⟩), mul_zero]
  · exact fun h => (h hi).elim

theorem degree_residuePoly_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (t z : ι → ℝ) :
    (residuePoly s t z).degree < (s.card : WithBot ℕ) := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (by simp)).mpr
  intro i hi
  calc
    (C (z i) * Lagrange.nodal (s.erase i) t).degree ≤ (Lagrange.nodal (s.erase i) t).degree :=
      by
        by_cases hz : z i = 0
        · simp [hz]
        · rw [degree_C_mul hz]
    _ = ((s.erase i).card : WithBot ℕ) := Lagrange.degree_nodal
    _ < (s.card : WithBot ℕ) := by exact_mod_cast card_erase_lt_of_mem hi

theorem X_mul_residuePoly {ι : Type*} [DecidableEq ι] (s : Finset ι) (t z : ι → ℝ) :
    X * residuePoly s t z = C (∑ i ∈ s, z i) * Lagrange.nodal s t +
      residuePoly s t (fun i => t i * z i) := by
  simp only [residuePoly, map_sum, sum_mul, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [Lagrange.nodal_eq_mul_nodal_erase hi, map_mul]
  ring

theorem X_pow_mul_residuePoly_of_moments {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) (k : ℕ)
    (hm : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0) :
    X^k * residuePoly s t z = residuePoly s t (fun i => (t i)^k * z i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih (fun j hj => hm j (hj.trans (Nat.lt_succ_self k))),
      X_mul_residuePoly]
    have hs : (∑ i ∈ s, (t i)^k * z i) = 0 := hm k (Nat.lt_succ_self k)
    rw [hs, map_zero, zero_mul, zero_add]
    congr 1
    funext i
    rw [pow_succ']
    ring

theorem degree_residuePoly_moments {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) (k : ℕ)
    (hm : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0) :
    (residuePoly s t z).degree + k < (s.card : WithBot ℕ) := by
  have hd := degree_residuePoly_lt s t (fun i => (t i)^k * z i)
  rw [← X_pow_mul_residuePoly_of_moments s t z k hm, degree_mul, degree_X_pow,
    add_comm] at hd
  exact hd

theorem residuePoly_ne_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {t z : ι → ℝ}
    (ht : Set.InjOn t s) {i : ι} (hi : i ∈ s) (hz : z i ≠ 0) :
    residuePoly s t z ≠ 0 := by
  intro he
  have hv := eval_residuePoly (z := z) ht hi
  rw [he, eval_zero] at hv
  have hp : (∏ j ∈ s.erase i, (t i - t j)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun he => (mem_erase.mp hj).1 ((ht hi (mem_erase.mp hj).2 he).symm))
  exact mul_ne_zero hz hp hv.symm

/-- Vanishing k moments on at most k distinct nodes forces every weight to vanish. -/
theorem weights_zero_of_moments {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {t z : ι → ℝ} (ht : Set.InjOn t s) {k : ℕ} (hk : s.card ≤ k)
    (hm : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0) : ∀ i ∈ s, z i = 0 := by
  intro i hi
  by_contra hz
  have hp := residuePoly_ne_zero ht hi hz
  have hd := degree_residuePoly_moments s t z k hm
  rw [degree_eq_natDegree hp] at hd
  have hn : (residuePoly s t z).natDegree + k < s.card := by exact_mod_cast hd
  omega

end
end SPR.N5.Direct
