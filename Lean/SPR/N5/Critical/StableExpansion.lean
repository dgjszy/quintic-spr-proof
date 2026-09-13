import SPR.N5.Critical.CoefficientGeometry
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# StableExpansion

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
证明稳定族存在仍稳定的非退化小扩张，覆盖主定理中的退化区间。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial Set Metric

theorem bounded_quintic_coefficient {v : Coeff5} {B : ℝ} (hv : ‖v‖ ≤ B)
    {n : ℕ} (hn : n < 5) : ‖((polynomial5 v).toPoly.map (algebraMap ℝ ℂ)).coeff n‖ ≤ B := by
  have h (i : Fin 5) : ‖v i‖ ≤ B := (norm_le_pi_norm v i).trans hv
  interval_cases n
  · simpa [polynomial5, Poly5.toPoly, coeff_add, coeff_mul_X_pow, coeff_X_pow,
      coeff_C, Polynomial.coeff_map] using h 4
  · simpa [polynomial5, Poly5.toPoly, coeff_add, coeff_mul_X_pow, coeff_X_pow,
      coeff_C, Polynomial.coeff_map] using h 3
  · simpa [polynomial5, Poly5.toPoly, coeff_add, coeff_mul_X_pow, coeff_X_pow,
      coeff_C, Polynomial.coeff_map] using h 2
  · simpa [polynomial5, Poly5.toPoly, coeff_add, coeff_mul_X_pow, coeff_X_pow,
      coeff_C, Polynomial.coeff_map] using h 1
  · simpa [polynomial5, Poly5.toPoly, coeff_add, coeff_mul_X_pow, coeff_X_pow,
      coeff_C, Polynomial.coeff_map] using h 0

theorem bounded_quintic_roots {v : Coeff5} {B : ℝ} (hB : 0 ≤ B) (hv : ‖v‖ ≤ B)
    {z : ℂ} (hz : ((polynomial5 v).toPoly.map (algebraMap ℝ ℂ)).IsRoot z) : ‖z‖ ≤ B + 1 := by
  let p := (polynomial5 v).toPoly.map (algebraMap ℝ ℂ)
  have hm : p.Monic := (quintic_monic _).map _
  have hd : p.natDegree = 5 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact quintic_natDegree _
  have hc : (p.cauchyBound : ℝ) ≤ B + 1 := by
    simp only [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hd]
    rw [NNReal.coe_add, NNReal.coe_one]
    suffices (↑(Finset.sup (Finset.range 5) (fun n => ‖p.coeff n‖₊)) : ℝ) ≤ B by linarith
    change (↑(Finset.sup (Finset.range 5) (fun n => ‖p.coeff n‖₊)) : ℝ) ≤ B
    rw [← NNReal.coe_mk B hB, NNReal.coe_le_coe]
    apply Finset.sup_le
    intro n hn
    exact_mod_cast bounded_quintic_coefficient hv (Finset.mem_range.mp hn)
  have hh : ‖z‖ < (p.cauchyBound : ℝ) := by
    exact_mod_cast hz.norm_lt_cauchyBound hm.ne_zero
  exact hh.le.trans hc

def unstableCoefficientSet (B : ℝ) : Set Coeff5 := Prod.fst ''
  ((closedBall (0 : Coeff5) B ×ˢ closedBall (0 : ℂ) (B + 1)) ∩
    {p : Coeff5 × ℂ | 0 ≤ p.2.re ∧
      ((polynomial5 p.1).toPoly.map (algebraMap ℝ ℂ)).eval p.2 = 0})

theorem compact_unstableCoefficientSet (B : ℝ) : IsCompact (unstableCoefficientSet B) := by
  apply IsCompact.image _ continuous_fst
  apply ((isCompact_closedBall (0 : Coeff5) B).prod
    (isCompact_closedBall (0 : ℂ) (B + 1))).inter_right
  exact (isClosed_le (g := fun p : Coeff5 × ℂ => p.2.re) continuous_const (by fun_prop)).inter
    (isClosed_eq continuous_coefficient_eval continuous_const)

theorem mem_unstableCoefficientSet_not_hurwitz {B : ℝ} {v : Coeff5}
    (hv : v ∈ unstableCoefficientSet B) : ¬ IsHurwitz (polynomial5 v).toPoly := by
  obtain ⟨⟨w,z⟩, h, he⟩ := hv
  dsimp at he
  subst w
  intro hs
  exact (not_lt_of_ge h.2.1) (hs z h.2.2)

theorem not_hurwitz_mem_unstableCoefficientSet {B : ℝ} (hB : 0 ≤ B) {v : Coeff5}
    (hv : ‖v‖ ≤ B) (hs : ¬ IsHurwitz (polynomial5 v).toPoly) :
    v ∈ unstableCoefficientSet B := by
  simp only [IsHurwitz, not_forall, not_lt] at hs
  obtain ⟨z, hz, hre⟩ := hs
  refine ⟨(v,z), ⟨⟨?_, ?_⟩, hre, hz⟩, rfl⟩
  · simpa using hv
  · simpa using bounded_quintic_roots hB hv hz

theorem Box5.exists_stable_fullWidth_expansion (K : Box5)
    (hK : ∀ a, K.Contains a → IsHurwitz a.toPoly) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      (∀ a, (K.expand ε hε.le).Contains a → IsHurwitz a.toPoly) ∧
      (K.expand ε hε.le).FullWidth := by
  let B := K.coefficientBound
  have hs : K.coefficientSet ⊆ (unstableCoefficientSet B)ᶜ := by
    intro v hv hb
    exact mem_unstableCoefficientSet_not_hurwitz hb (hK _ ((K.mem_coefficientSet v).mp hv))
  obtain ⟨δ, hδ, hd⟩ := K.compact_coefficientSet.exists_thickening_subset_open
    (compact_unstableCoefficientSet B).isClosed.isOpen_compl hs
  let ε := min (δ / 2) 1
  have hε : 0 < ε := lt_min (by linarith) zero_lt_one
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ε, hε, ?_, K.expand_fullWidth hε⟩
  intro a ha
  let v := coefficients5 a
  have hv : v ∈ (K.expand ε hε.le).coefficientSet := (K.expand ε hε.le).coefficients_mem ha
  have hn : ‖v‖ ≤ B := K.expanded_norm_bound hε.le (min_le_right _ _) hv
  have ht : v ∈ thickening δ K.coefficientSet := by
    apply mem_thickening_iff.mpr
    exact ⟨K.clipCoefficients v, K.clipCoefficients_mem v,
      (K.dist_clip_le hε.le hv).trans_lt hεδ⟩
  have hstable : IsHurwitz (polynomial5 v).toPoly := by
    by_contra hh
    exact hd ht (not_hurwitz_mem_unstableCoefficientSet K.coefficientBound_pos.le hn hh)
  simpa [v, polynomial5_coefficients5] using hstable

end
end SPR.N5.Direct
