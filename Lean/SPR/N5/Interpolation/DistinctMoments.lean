import SPR.N5.Critical.MergedCertificate
import SPR.N5.Interpolation.MomentRigidity

/-!
# DistinctMoments

论文 §4.3：消失矩、插值恒等式及支持点个数。
对互异频率表示定义带权分量 z、y 及 U、V，证明矩等式和 U 非零。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial Finset

theorem numeratorEvenPoly_degree (b : Vec6) (hb1 : b 1 ≠ 0) :
    (numeratorEvenPoly b).natDegree = 2 := by
  unfold numeratorEvenPoly
  compute_degree!

theorem numeratorOddPoly_degree_le (b : Vec6) : (numeratorOddPoly b).natDegree ≤ 2 := by
  unfold numeratorOddPoly
  compute_degree!

theorem numeratorOddPoly_degree (b : Vec6) (hb0 : b 0 ≠ 0) :
    (numeratorOddPoly b).natDegree = 2 := by
  unfold numeratorOddPoly
  compute_degree!

theorem numeratorOddPoly_quartic_degree (b : Vec6) (hb0 : b 0 = 0) (hb2 : b 2 ≠ 0) :
    (numeratorOddPoly b).natDegree = 1 := by
  unfold numeratorOddPoly
  rw [hb0]
  simp only [map_zero, zero_mul, zero_sub]
  compute_degree!

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}
/-- 节点处的带权偶部分量 μ_i E_i。 -/
def z (C : DistinctMomentCertificate K b) (r : ℝ) := C.μ r * evenPart (C.a r) r
/-- 节点处的带权奇部分量 μ_i t_i O_i。 -/
def y (C : DistinctMomentCertificate K b) (r : ℝ) := C.μ r * (r * oddPart (C.a r) r)
/-- 对带权偶部分量构造的插值多项式 U=R_z。 -/
def U (C : DistinctMomentCertificate K b) : ℝ[X] := residuePoly C.nodes id C.z
/-- 对带权奇部分量构造的插值多项式 V=R_y。 -/
def V (C : DistinctMomentCertificate K b) : ℝ[X] := residuePoly C.nodes id C.y

theorem moments (C : DistinctMomentCertificate K b) :
    (∑ r ∈ C.nodes, C.z r) = 0 ∧
    (∑ r ∈ C.nodes, r * C.z r) = 0 ∧
    (∑ r ∈ C.nodes, r^2 * C.z r) = 0 ∧
    (∑ r ∈ C.nodes, C.y r) = 0 ∧
    (∑ r ∈ C.nodes, r * C.y r) = 0 ∧
    (∑ r ∈ C.nodes, r^2 * C.y r) = -C.μinf := by
  have hh : ∀ j : Fin 6, (∑ r ∈ C.nodes, C.μ r * feature (C.a r) r j) +
      C.μinf * infinityFeature j = 0 := by
    intro j
    simpa only [sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun v : Vec6 => v j) C.balance
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  have h5 := hh 5
  dsimp [feature, infinityFeature] at h0 h1 h2 h3 h4 h5
  simp only [mul_zero, mul_one, add_zero, mul_neg, sum_neg_distrib, neg_eq_zero] at h0 h1 h2 h3 h4 h5
  dsimp [z,y]
  constructor
  · exact h5
  constructor
  · simpa only [mul_left_comm] using h3
  constructor
  · simpa only [mul_left_comm] using h1
  constructor
  · exact h4
  constructor
  · calc
      _ = ∑ r ∈ C.nodes, C.μ r * (r^2 * oddPart (C.a r) r) := sum_congr rfl (fun r _ => by ring)
      _ = 0 := h2
  · have he : (∑ r ∈ C.nodes, C.μ r * (r^3 * oddPart (C.a r) r)) = -C.μinf := by linarith
    calc
      _ = ∑ r ∈ C.nodes, C.μ r * (r^3 * oddPart (C.a r) r) := sum_congr rfl (fun r _ => by ring)
      _ = -C.μinf := he

theorem z_moments (C : DistinctMomentCertificate K b) :
    ∀ j < 3, (∑ r ∈ C.nodes, r^j * C.z r) = 0 := by
  intro j hj
  interval_cases j
  · simpa using C.moments.1
  · simpa using C.moments.2.1
  · exact C.moments.2.2.1

theorem y_moments (C : DistinctMomentCertificate K b) :
    ∀ j < 2, (∑ r ∈ C.nodes, r^j * C.y r) = 0 := by
  intro j hj
  interval_cases j
  · simpa using C.moments.2.2.2.1
  · simpa using C.moments.2.2.2.2.1

theorem y_three_moments (C : DistinctMomentCertificate K b) (hi : C.μinf = 0) :
    ∀ j < 3, (∑ r ∈ C.nodes, r^j * C.y r) = 0 := by
  intro j hj
  by_cases hj2 : j < 2
  · exact C.y_moments j hj2
  · have he : j = 2 := by omega
    simpa [he, hi] using C.moments.2.2.2.2.2

theorem z_ne_zero (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r : ℝ} (hr : r ∈ C.nodes) : C.z r ≠ 0 := by
  apply mul_ne_zero (ne_of_gt (C.positive r hr))
  by_cases hr0 : r = 0
  · subst r
    simpa [evenPart] using ne_of_gt (quintic_constant_pos (hK _ (C.contains 0 hr)))
  · exact (K.positive_contact_denominator_components_ne_zero hK hwidth hb hw
      (C.contains r hr) (lt_of_le_of_ne (C.nonneg r hr) (Ne.symm hr0)) (C.contacts r hr)).1

theorem U_ne_zero (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    C.U ≠ 0 := by
  obtain ⟨r,hr⟩ := C.nonempty
  exact residuePoly_ne_zero (Function.injective_id.injOn) hr (C.z_ne_zero hK hwidth hb hw hr)

theorem residue_identity (C : DistinctMomentCertificate K b) (hb1 : b 1 ≠ 0) :
    numeratorEvenPoly b * C.U + numeratorOddPoly b * C.V = 0 := by
  apply contact_residue_identity C.nodes id C.z C.y Function.injective_id.injOn
  · exact (degree_le_natDegree).trans (by rw [numeratorEvenPoly_degree b hb1]; norm_num)
  · exact (degree_le_natDegree).trans (by exact_mod_cast numeratorOddPoly_degree_le b)
  · exact fun j hj => C.z_moments j (by omega)
  · exact C.y_moments
  · intro r hr
    simp only [id_eq, numeratorEvenPoly_eval, numeratorOddPoly_eval,z,y]
    have hc := C.contacts r hr
    unfold generalPairing at hc
    calc
      _ = C.μ r * (numeratorEven b r * evenPart (C.a r) r +
        r * (numeratorOdd b r * oddPart (C.a r) r)) := by ring
      _ = 0 := by rw [hc,mul_zero]

end DistinctMomentCertificate
end
end SPR.N5.Direct
