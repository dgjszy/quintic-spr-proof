import SPR.N5.Preliminaries.HurwitzPhase

/-! The precise fifth-degree Hermite-Biehler interlacing needed here.
## 与论文的对应

论文 §2：Hurwitz 稳定性、零点交错及统一分母零点区间。
相位论证给出偶奇部分的简单正根及严格交错。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Filter Set
open scoped Topology

theorem rootPhase_hits {a : Poly5} (ha : IsHurwitz a.toPoly) {y : ℝ}
    (hy0 : 0 < y) (hy : y < 5 * Real.pi / 2) :
    ∃ ω : ℝ, 0 < ω ∧ rootPhase a ω = y := by
  have he : ∀ᶠ ω : ℝ in atTop, y < rootPhase a ω :=
    (rootPhase_tendsto ha).eventually (lt_mem_nhds hy)
  obtain ⟨w, hw0, hwy⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  have hymem : y ∈ Icc (rootPhase a 0) (rootPhase a w) := by
    rw [rootPhase_zero]
    exact ⟨hy0.le, hwy.le⟩
  obtain ⟨ω, hω, hphase⟩ := intermediate_value_Icc hw0.le
    (rootPhase_continuous ha).continuousOn hymem
  have hω0 : 0 < ω := lt_of_le_of_ne hω.1 (by
    intro heq
    have h := hphase
    rw [← heq, rootPhase_zero] at h
    linarith)
  exact ⟨ω, hω0, hphase⟩

theorem hurwitz_interlacing_roots {a : Poly5} (ha : IsHurwitz a.toPoly) :
    ∃ e₁ o₁ e₂ o₂ : ℝ, 0 < e₁ ∧ e₁ < o₁ ∧ o₁ < e₂ ∧ e₂ < o₂ ∧
      evenPart a e₁ = 0 ∧ oddPart a o₁ = 0 ∧ evenPart a e₂ = 0 ∧ oddPart a o₂ = 0 := by
  have hp := Real.pi_pos
  obtain ⟨v₁, hv₁, h₁⟩ := rootPhase_hits ha (y := Real.pi / 2) (by linarith) (by linarith)
  obtain ⟨v₂, hv₂, h₂⟩ := rootPhase_hits ha (y := Real.pi) hp (by linarith)
  obtain ⟨v₃, hv₃, h₃⟩ := rootPhase_hits ha (y := Real.pi / 2 + Real.pi)
    (by linarith) (by linarith)
  obtain ⟨v₄, hv₄, h₄⟩ := rootPhase_hits ha (y := Real.pi + Real.pi)
    (by linarith) (by linarith)
  have hv12 : v₁ < v₂ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₁, h₂]; linarith)
  have hv23 : v₂ < v₃ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₂, h₃]; linarith)
  have hv34 : v₃ < v₄ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₃, h₄]; linarith)
  refine ⟨v₁ ^ 2, v₂ ^ 2, v₃ ^ 2, v₄ ^ 2, sq_pos_of_pos hv₁,
    (sq_lt_sq₀ hv₁.le hv₂.le).mpr hv12, (sq_lt_sq₀ hv₂.le hv₃.le).mpr hv23,
    (sq_lt_sq₀ hv₃.le hv₄.le).mpr hv34, ?_, ?_, ?_, ?_⟩
  · simpa [h₁] using frequencyValue_phase_re ha v₁
  · have h := frequencyValue_phase_im ha v₂
    simp only [h₂, Real.sin_pi, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hv₂)
  · simpa [h₃, Real.cos_add] using frequencyValue_phase_re ha v₃
  · have h := frequencyValue_phase_im ha v₄
    simp only [h₄, Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hv₄)

theorem quadratic_factor_of_two_roots {p : ℝ[X]} (hdeg : p.natDegree ≤ 2)
    {r s : ℝ} (hrs : r ≠ s) (hr : p.eval r = 0) (hs : p.eval s = 0) :
    p = C (p.coeff 2) * ((X - C r) * (X - C s)) := by
  have hmonic := (monic_X_sub_C r).mul (monic_X_sub_C s)
  have hdvd := (distinct_linear_coprime hrs).mul_dvd
    (dvd_iff_isRoot.mpr hr) (dvd_iff_isRoot.mpr hs)
  have hbase : ((X - C r) * (X - C s) : ℝ[X]).natDegree = 2 := by
    rw [(monic_X_sub_C r).natDegree_mul (monic_X_sub_C s)]
    simp
  have hform := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    hmonic hdvd (by rwa [hbase])
  have hc : p.coeff 2 = p.leadingCoeff := by
    conv_lhs => rw [hform]
    rw [coeff_C_mul, ← hbase, coeff_natDegree, hmonic.leadingCoeff, mul_one]
  rwa [hc]

structure DenominatorInterlacing (a : Poly5) where
  e₁ : ℝ
  o₁ : ℝ
  e₂ : ℝ
  o₂ : ℝ
  e₁_pos : 0 < e₁
  e₁_lt_o₁ : e₁ < o₁
  o₁_lt_e₂ : o₁ < e₂
  e₂_lt_o₂ : e₂ < o₂
  even_factor : denominatorEvenPoly a = C a.a1 * ((X - C e₁) * (X - C e₂))
  odd_factor : denominatorOddPoly a = (X - C o₁) * (X - C o₂)

theorem denominator_interlacing {a : Poly5} (ha : IsHurwitz a.toPoly) :
    Nonempty (DenominatorInterlacing a) := by
  obtain ⟨e₁, o₁, e₂, o₂, he, heo, hoe, heo', hE₁, hO₁, hE₂, hO₂⟩ :=
    hurwitz_interlacing_roots ha
  have hedeg : (denominatorEvenPoly a).natDegree ≤ 2 := by
    unfold denominatorEvenPoly
    compute_degree!
  have hodeg : (denominatorOddPoly a).natDegree ≤ 2 := by
    unfold denominatorOddPoly
    compute_degree!
  have hEe (t : ℝ) : (denominatorEvenPoly a).eval t = evenPart a t := by
    simp [denominatorEvenPoly, evenPart]
  have hOo (t : ℝ) : (denominatorOddPoly a).eval t = oddPart a t := by
    simp [denominatorOddPoly, oddPart]
  have hEf := quadratic_factor_of_two_roots hedeg (ne_of_lt (heo.trans hoe))
    (by rwa [hEe]) (by rwa [hEe])
  have hOf := quadratic_factor_of_two_roots hodeg (ne_of_lt (hoe.trans heo'))
    (by rwa [hOo]) (by rwa [hOo])
  refine ⟨⟨e₁, o₁, e₂, o₂, he, heo, hoe, heo', ?_, ?_⟩⟩
  · simpa [denominatorEvenPoly, coeff_sub, coeff_add, coeff_C_mul_X_pow] using hEf
  · simpa [denominatorOddPoly, coeff_sub, coeff_add] using hOf

end
end SPR.N5.Direct
