import SPR.N5.Interpolation.ConstantMultiplier

/-!
# InterpolationSigns

论文 §4.3：消失矩、插值恒等式及支持点个数。
在节点处求值常数倍恒等式，连接正权重、分子分量和插值权重符号。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial Finset

theorem residuePoly_top_coefficient {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) :
    (residuePoly s t z).coeff (s.card - 1) = ∑ i ∈ s, z i := by
  simp only [residuePoly,finsetSum_coeff,coeff_C_mul]
  apply sum_congr rfl
  intro i hi
  have hd : (Lagrange.nodal (s.erase i) t).natDegree = s.card - 1 := by
    rw [Lagrange.natDegree_nodal,card_erase_of_mem hi]
  rw [← hd,coeff_natDegree,(Lagrange.nodal_monic (s := s.erase i) (v := t)).leadingCoeff,mul_one]

theorem residuePoly_first_coefficient {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) {k d : ℕ} (hcard : s.card - 1 = d + k)
    (hm : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0) :
    (residuePoly s t z).coeff d = ∑ i ∈ s, (t i)^k * z i := by
  have he := congrArg (fun p : ℝ[X] => p.coeff (d+k))
    (X_pow_mul_residuePoly_of_moments s t z k hm)
  dsimp only at he
  rw [coeff_X_pow_mul,← hcard,residuePoly_top_coefficient] at he
  exact he

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem coefficient_V_two (C : DistinctMomentCertificate K b) (hn : C.nodes.card = 5) :
    C.V.coeff 2 = -C.μinf := by
  rw [V,residuePoly_first_coefficient C.nodes id C.y (k := 2) (by omega) C.y_moments]
  exact C.moments.2.2.2.2.2

theorem multiplier_positive_at_infinity (C : DistinctMomentCertificate K b)
    (hb1 : 0 < b 1) (hn : C.nodes.card = 5) (hi : 0 < C.μinf) {c : ℝ}
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) : 0 < c := by
  have he := C.coefficient_V_two hn
  rw [hV,coeff_neg,coeff_C_mul] at he
  have hc : (numeratorEvenPoly b).coeff 2 = b 1 := by
    simp [numeratorEvenPoly,coeff_add,coeff_sub,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
  rw [hc] at he
  have hp : 0 < c * b 1 := by linarith
  exact (mul_pos_iff_of_pos_right hb1).mp hp

/-- The exact nodal-weight identities used to determine denominator signs. -/
theorem node_multiplier_identities (C : DistinctMomentCertificate K b) {c : ℝ}
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) {r : ℝ} (hr : r ∈ C.nodes) :
    C.z r = c * Lagrange.nodalWeight C.nodes id r * numeratorOdd b r ∧
    C.y r = -(c * Lagrange.nodalWeight C.nodes id r * numeratorEven b r) := by
  have hu := congrArg (fun p : ℝ[X] => p.eval r) hU
  have hv := congrArg (fun p : ℝ[X] => p.eval r) hV
  simp only [U,V,eval_residuePoly Function.injective_id.injOn hr,
    eval_mul,eval_C,eval_neg,numeratorOddPoly_eval,numeratorEvenPoly_eval,id_eq] at hu hv
  have hu0 := eval_residuePoly (t := id) (z := C.z) Function.injective_id.injOn hr
  have hv0 := eval_residuePoly (t := id) (z := C.y) Function.injective_id.injOn hr
  dsimp only [id_eq] at hu0 hv0
  rw [hu0] at hu
  rw [hv0] at hv
  have hp : (∏ j ∈ C.nodes.erase r, (r-j)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (Ne.symm (mem_erase.mp hj).1)
  rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Lagrange.eval_nodal]
  dsimp only [id_eq]
  constructor <;> field_simp [hp] <;> nlinarith [hu,hv]

end DistinctMomentCertificate
end
end SPR.N5.Direct
