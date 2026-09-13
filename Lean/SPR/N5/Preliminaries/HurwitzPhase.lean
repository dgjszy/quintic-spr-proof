import SPR.N5.Preliminaries.HurwitzCoefficients

/-! A continuous increasing phase, with root multiplicities retained.
## 与论文的对应

论文 §2：Hurwitz 稳定性、零点交错及统一分母零点区间。
按重数计入复根，构造连续严格递增的相位并计算端点行为。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Filter Set
open scoped Topology Classical

def complexRootMultiset (a : Poly5) : Multiset ℂ :=
  (a.toPoly.map (algebraMap ℝ ℂ)).roots

theorem complexRootMultiset_card (a : Poly5) : (complexRootMultiset a).card = 5 := by
  rw [complexRootMultiset, ← (IsAlgClosed.splits _).natDegree_eq_card_roots]
  simp [quintic_natDegree]

theorem complexRootMultiset_re_neg {a : Poly5} (ha : IsHurwitz a.toPoly)
    (z : complexRootMultiset a) : (z : ℂ).re < 0 := by
  apply ha
  apply (mem_roots ((quintic_monic a).map (algebraMap ℝ ℂ)).ne_zero).mp
  exact Multiset.coe_mem (x := z)

theorem sum_map_eq_sum_occurrences {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (m : Multiset α) (f : α → β) : (m.map f).sum = ∑ z : m, f z := by
  rw [← m.map_univ f]
  rfl

theorem prod_map_eq_prod_occurrences {α β : Type*} [DecidableEq α] [CommMonoid β]
    (m : Multiset α) (f : α → β) : (m.map f).prod = ∏ z : m, f z := by
  rw [← m.map_univ f]
  rfl

theorem complexRootMultiset_conj (a : Poly5) :
    (complexRootMultiset a).map (starRingEnd ℂ) = complexRootMultiset a := by
  have hmap : (a.toPoly.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) =
      a.toPoly.map (algebraMap ℝ ℂ) := by
    ext n
    simp
  unfold complexRootMultiset
  rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (IsAlgClosed.splits _).natDegree_eq_card_roots.symm, hmap]

def rootPhase (a : Poly5) (ω : ℝ) : ℝ :=
  ∑ z : complexRootMultiset a, Real.arctan ((ω - (z : ℂ).im) / (-(z : ℂ).re))

def rootAmplitude (a : Poly5) (ω : ℝ) : ℝ :=
  ∏ z : complexRootMultiset a,
    (-(z : ℂ).re) / Real.cos (Real.arctan ((ω - (z : ℂ).im) / (-(z : ℂ).re)))

theorem rootPhase_zero (a : Poly5) : rootPhase a 0 = 0 := by
  let f : ℂ → ℝ := fun z => Real.arctan ((0 - z.im) / (-z.re))
  have hc := congrArg (fun m : Multiset ℂ => (m.map f).sum) (complexRootMultiset_conj a)
  have hf (z : ℂ) : f (starRingEnd ℂ z) = - f z := by
    simp [f, Real.arctan_neg, neg_div, div_neg]
  simp only [Multiset.map_map, Function.comp_apply, hf, Multiset.sum_map_neg] at hc
  have hp : rootPhase a 0 = ((complexRootMultiset a).map f).sum := by
    rw [sum_map_eq_sum_occurrences]
    rfl
  rw [hp]
  linarith

theorem rootPhase_continuous {a : Poly5} (ha : IsHurwitz a.toPoly) :
    Continuous (rootPhase a) := by
  unfold rootPhase
  apply continuous_finsetSum
  intro z _
  exact Real.continuous_arctan.comp
    ((continuous_id.sub continuous_const).div_const _)

theorem rootPhase_strictMono {a : Poly5} (ha : IsHurwitz a.toPoly) :
    StrictMono (rootPhase a) := by
  intro x y hxy
  unfold rootPhase
  apply Finset.sum_lt_sum
  · intro z _
    exact (Real.arctan_strictMono (div_lt_div_of_pos_right
      (sub_lt_sub_right hxy _) (neg_pos.mpr (complexRootMultiset_re_neg ha z)))).le
  · have hcard : Fintype.card (complexRootMultiset a) = 5 := by
      rw [Multiset.card_coe, complexRootMultiset_card]
    haveI : Nonempty (complexRootMultiset a) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨z⟩ := ‹Nonempty (complexRootMultiset a)›
    exact ⟨z, Finset.mem_univ z, Real.arctan_strictMono (div_lt_div_of_pos_right
      (sub_lt_sub_right hxy _) (neg_pos.mpr (complexRootMultiset_re_neg ha z)))⟩

theorem rootPhase_tendsto {a : Poly5} (ha : IsHurwitz a.toPoly) :
    Tendsto (rootPhase a) atTop (𝓝 (5 * Real.pi / 2)) := by
  have h (z : complexRootMultiset a) :
      Tendsto (fun ω : ℝ => Real.arctan ((ω - (z : ℂ).im) / (-(z : ℂ).re)))
        atTop (𝓝 (Real.pi / 2)) := by
    apply Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
    exact (tendsto_atTop_add_const_right atTop (-(z : ℂ).im) tendsto_id).atTop_div_const
      (neg_pos.mpr (complexRootMultiset_re_neg ha z))
  have hs := tendsto_finsetSum Finset.univ (fun z _ => h z)
  change Tendsto (fun ω => ∑ z : complexRootMultiset a,
    Real.arctan ((ω - (z : ℂ).im) / (-(z : ℂ).re))) atTop _
  simpa [Multiset.card_coe, complexRootMultiset_card, nsmul_eq_mul, mul_div_assoc] using hs

theorem rootAmplitude_pos {a : Poly5} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    0 < rootAmplitude a ω := by
  apply Finset.prod_pos
  intro z _
  exact div_pos (neg_pos.mpr (complexRootMultiset_re_neg ha z)) (Real.cos_arctan_pos _)

theorem linear_factor_phase {r y : ℝ} (hr : 0 < r) :
    (r : ℂ) + Complex.I * (y : ℂ) =
      ((r / Real.cos (Real.arctan (y / r)) : ℝ) : ℂ) *
        Complex.exp ((Real.arctan (y / r) : ℂ) * Complex.I) := by
  have hc := ne_of_gt (Real.cos_arctan_pos (y / r))
  have hs : Real.sin (Real.arctan (y / r)) =
      (y / r) * Real.cos (Real.arctan (y / r)) := by
    have h := Real.tan_arctan (y / r)
    rw [Real.tan_eq_sin_div_cos] at h
    exact (div_eq_iff hc).mp h
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero, hs]
  · field_simp
  · field_simp

theorem frequencyValue_phase {a : Poly5} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    frequencyValue a ω = (rootAmplitude a ω : ℂ) *
      Complex.exp ((rootPhase a ω : ℂ) * Complex.I) := by
  rw [frequencyValue, (IsAlgClosed.splits _).eval_eq_prod_roots_of_monic
    ((quintic_monic a).map (algebraMap ℝ ℂ)), prod_map_eq_prod_occurrences]
  change (∏ z : complexRootMultiset a, (Complex.I * (ω : ℂ) - (z : ℂ))) = _
  have hf (z : complexRootMultiset a) : Complex.I * (ω : ℂ) - (z : ℂ) =
      (((-(z : ℂ).re) / Real.cos
        (Real.arctan ((ω - (z : ℂ).im) / (-(z : ℂ).re))) : ℝ) : ℂ) *
      Complex.exp ((Real.arctan ((ω - (z : ℂ).im) / (-(z : ℂ).re)) : ℂ) * Complex.I) := by
    rw [← linear_factor_phase (neg_pos.mpr (complexRootMultiset_re_neg ha z))]
    apply Complex.ext <;> simp <;> ring
  simp only [hf, Finset.prod_mul_distrib]
  congr 1
  · simp [rootAmplitude]
  · rw [← Complex.exp_sum]
    congr 1
    simp [rootPhase, Finset.sum_mul]

theorem frequencyValue_phase_re {a : Poly5} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    evenPart a (ω ^ 2) = rootAmplitude a ω * Real.cos (rootPhase a ω) := by
  have h := congrArg Complex.re (frequencyValue_phase ha ω)
  simpa [frequencyValue_re, Complex.exp_mul_I] using h

theorem frequencyValue_phase_im {a : Poly5} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    ω * oddPart a (ω ^ 2) = rootAmplitude a ω * Real.sin (rootPhase a ω) := by
  have h := congrArg Complex.im (frequencyValue_phase ha ω)
  simpa [frequencyValue_im, Complex.exp_mul_I] using h

end
end SPR.N5.Direct
