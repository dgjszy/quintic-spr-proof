import SPR.N5.Critical.FullWidthCritical

/-!
# CoefficientAverages

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
在相同频率处对分母按权重取平均；证明区间成员性和配对恒等式保持。
-/

namespace SPR.N5.Direct
noncomputable section
open Finset Set

def averagePoly {ι : Type*} (s : Finset ι) (w : ι → ℝ) (a : ι → Poly5) : Poly5 :=
  polynomial5 (s.centerMass w (fun i => coefficients5 (a i)))

theorem Box5.averagePoly_mem {ι : Type*} (K : Box5) (s : Finset ι)
    (w : ι → ℝ) (a : ι → Poly5) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) (ha : ∀ i ∈ s, K.Contains (a i)) :
    K.Contains (averagePoly s w a) := by
  apply (K.mem_coefficientSet _).mp
  exact (convex_Icc _ _).centerMass_mem hw hW (fun i hi => K.coefficients_mem (ha i hi))

theorem averagePoly_coordinate {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → Poly5) (j : Fin 5) :
    coefficients5 (averagePoly s w a) j =
      (∑ i ∈ s, w i)⁻¹ * (∑ i ∈ s, w i * coefficients5 (a i) j) := by
  simp [averagePoly, coefficients5_polynomial5, Finset.centerMass, sum_apply]

theorem averagePoly_even {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → Poly5) (r : ℝ) (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i) * evenPart (averagePoly s w a) r =
      ∑ i ∈ s, w i * evenPart (a i) r := by
  have h0 := averagePoly_coordinate s w a 0
  have h2 := averagePoly_coordinate s w a 2
  have h4 := averagePoly_coordinate s w a 4
  change (averagePoly s w a).a1 = (∑ i ∈ s, w i)⁻¹ * (∑ i ∈ s, w i * (a i).a1) at h0
  change (averagePoly s w a).a3 = (∑ i ∈ s, w i)⁻¹ * (∑ i ∈ s, w i * (a i).a3) at h2
  change (averagePoly s w a).a5 = (∑ i ∈ s, w i)⁻¹ * (∑ i ∈ s, w i * (a i).a5) at h4
  simp only [evenPart, h0, h2, h4, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib,
    ← mul_assoc, ← sum_mul]
  field_simp [hW]

theorem averagePoly_odd {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → Poly5) (r : ℝ) (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i) * oddPart (averagePoly s w a) r =
      ∑ i ∈ s, w i * oddPart (a i) r := by
  have h1 := averagePoly_coordinate s w a 1
  have h3 := averagePoly_coordinate s w a 3
  change (averagePoly s w a).a2 = (∑ i ∈ s, w i)⁻¹ * (∑ i ∈ s, w i * (a i).a2) at h1
  change (averagePoly s w a).a4 = (∑ i ∈ s, w i)⁻¹ * (∑ i ∈ s, w i * (a i).a4) at h3
  simp only [oddPart, h1, h3, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib,
    ← mul_assoc, ← sum_mul]
  field_simp [hW]

theorem averagePoly_feature {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → Poly5) (r : ℝ) (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i) • feature (averagePoly s w a) r =
      ∑ i ∈ s, w i • feature (a i) r := by
  have hE := averagePoly_even s w a r hW
  have hO := averagePoly_odd s w a r hW
  ext j
  fin_cases j <;>
    norm_num [feature, Pi.smul_apply, smul_eq_mul, sum_apply,
      mul_left_comm (w _), ← Finset.mul_sum] <;>
    first | (rw [← hE]; ring) | (rw [← hO]; ring) | exact hE

theorem averagePoly_contact {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → Poly5) (b : Vec6) (r : ℝ) (hW : (∑ i ∈ s, w i) ≠ 0)
    (hc : ∀ i ∈ s, generalPairing (a i) b r = 0) :
    generalPairing (averagePoly s w a) b r = 0 := by
  have hE := averagePoly_even s w a r hW
  have hO := averagePoly_odd s w a r hW
  have hh : (∑ i ∈ s, w i) * generalPairing (averagePoly s w a) b r =
      ∑ i ∈ s, w i * generalPairing (a i) b r := by
    simp only [generalPairing, mul_add, sum_add_distrib]
    simp_rw [mul_left_comm (w _), ← mul_sum]
    rw [← hE, ← hO]
    ring
  have hz : (∑ i ∈ s, w i * generalPairing (a i) b r) = 0 :=
    sum_eq_zero (fun i hi => by rw [hc i hi, mul_zero])
  exact (mul_eq_zero.mp (hh.trans hz)).resolve_left hW

end
end SPR.N5.Direct
