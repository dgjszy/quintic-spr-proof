import SPR.N5.Interpolation.DistinctMoments

/-!
# Constant interpolation multiplier and the two support shapes

Paper §4.3, equations (4.7)–(4.12) and Proposition 4.5. Vanishing moments bound
`V` by degree two in either infinity branch. Coprimality then turns the contact
identity into `U = c O_b`, `V = -c E_b`, with `c ≠ 0`. The exact degree of `V`
forces either five finite nodes and positive infinity mass, or six finite nodes.

## 与论文的对应

论文 §4.3：消失矩、插值恒等式及支持点个数。
用次数界迫使公共倍数为非零常数，再由 V 的精确次数确定两种支持形态。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial Finset

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

/-- The two always-vanishing odd moments give `deg V + 2 < m`. -/
theorem V_natDegree_add_two_lt_card (C : DistinctMomentCertificate K b)
    (hV : C.V ≠ 0) : C.V.natDegree + 2 < C.nodes.card := by
  have hdegree := degree_residuePoly_moments C.nodes id C.y 2 C.y_moments
  change C.V.degree + 2 < (C.nodes.card : WithBot ℕ) at hdegree
  rw [degree_eq_natDegree hV] at hdegree
  exact_mod_cast hdegree

/-- With no infinity mass, the third odd moment also vanishes. -/
theorem V_natDegree_add_three_lt_card (C : DistinctMomentCertificate K b)
    (hV : C.V ≠ 0) (hinfinity : C.μinf = 0) :
    C.V.natDegree + 3 < C.nodes.card := by
  have hdegree := degree_residuePoly_moments C.nodes id C.y 3
    (C.y_three_moments hinfinity)
  change C.V.degree + 3 < (C.nodes.card : WithBot ℕ) at hdegree
  rw [degree_eq_natDegree hV] at hdegree
  exact_mod_cast hdegree

/-- Combining the support bound with either moment bound gives `deg V ≤ 2`. -/
theorem V_natDegree_le_two (C : DistinctMomentCertificate K b) (hV : C.V ≠ 0) :
    C.V.natDegree ≤ 2 := by
  have hsize := C.size
  by_cases hinfinity : C.μinf = 0
  · have hdegree := C.V_natDegree_add_three_lt_card hV hinfinity
    omega
  · have hpositive : 0 < C.μinf :=
      lt_of_le_of_ne C.infinity_nonneg (Ne.symm hinfinity)
    rw [if_pos hpositive] at hsize
    have hdegree := C.V_natDegree_add_two_lt_card hV
    omega

/-- Coprimality and the degree bound force a nonzero constant multiplier. -/
theorem constant_multiplier (C : DistinctMomentCertificate K b) (hU : C.U ≠ 0)
    (hb1 : b 1 ≠ 0) (hcop : IsCoprime (numeratorEvenPoly b) (numeratorOddPoly b)) :
    ∃ c : ℝ, c ≠ 0 ∧ C.U = Polynomial.C c * numeratorOddPoly b ∧
      C.V = -(Polynomial.C c * numeratorEvenPoly b) := by
  have hE : numeratorEvenPoly b ≠ 0 := by
    intro hzero
    have hdegree := numeratorEvenPoly_degree b hb1
    rw [hzero, natDegree_zero] at hdegree
    omega
  -- First obtain a polynomial multiplier. Nonzero U ensures that Q is nonzero.
  obtain ⟨Q, hV, hUf⟩ := coprime_contact_multiplier hcop hE (C.residue_identity hb1)
  have hQ : Q ≠ 0 := by
    intro hzero
    simp only [hzero, mul_zero, neg_zero] at hUf
    exact hU hUf
  have hVne : C.V ≠ 0 := by
    rw [hV]
    exact mul_ne_zero hE hQ
  have hdegree : C.V.natDegree = 2 + Q.natDegree := by
    rw [hV, natDegree_mul hE hQ, numeratorEvenPoly_degree b hb1]
  -- Only now compare exact degrees; no degree calculation is made for a zero Q.
  have hQdegree : Q.natDegree = 0 := by
    have hbound := C.V_natDegree_le_two hVne
    omega
  have hconstant : Q = Polynomial.C (Q.coeff 0) := eq_C_of_natDegree_eq_zero hQdegree
  refine ⟨-(Q.coeff 0), ?_, ?_, ?_⟩
  · intro hzero
    have hcoeff : Q.coeff 0 = 0 := neg_eq_zero.mp hzero
    exact hQ (by rw [hconstant, hcoeff, map_zero])
  · rw [hUf, hconstant, map_neg, coeff_C_zero]
    ring
  · rw [hV, hconstant, map_neg, coeff_C_zero]
    ring

/-- Paper Proposition 4.5: the nonzero quadratic V saturates the support bound. -/
theorem support_dichotomy (C : DistinctMomentCertificate K b) (hU : C.U ≠ 0)
    (hb1 : b 1 ≠ 0) (hcop : IsCoprime (numeratorEvenPoly b) (numeratorOddPoly b)) :
    (C.nodes.card = 5 ∧ 0 < C.μinf ∧ b 0 = 0) ∨
      (C.nodes.card = 6 ∧ C.μinf = 0) := by
  obtain ⟨c, hc, _, hV⟩ := C.constant_multiplier hU hb1 hcop
  have hdegree : C.V.natDegree = 2 := by
    rw [hV, natDegree_neg, natDegree_C_mul hc, numeratorEvenPoly_degree b hb1]
  have hVne : C.V ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hdegree
    omega
  have hsize := C.size
  by_cases hinfinity : C.μinf = 0
  · have hbound := C.V_natDegree_add_three_lt_card hVne hinfinity
    exact Or.inr ⟨by omega, hinfinity⟩
  · have hpositive : 0 < C.μinf :=
      lt_of_le_of_ne C.infinity_nonneg (Ne.symm hinfinity)
    rw [if_pos hpositive] at hsize
    have hbound := C.V_natDegree_add_two_lt_card hVne
    have hbzero : b 0 = 0 := (mul_eq_zero.mp C.infinity_contact).resolve_left hinfinity
    exact Or.inl ⟨by omega, hpositive, hbzero⟩

end DistinctMomentCertificate
end
end SPR.N5.Direct
