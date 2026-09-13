import SPR.N5.Critical.CriticalSupport
import SPR.N5.Critical.CertificateMoments

/-! A nontrivial finite-frequency certificate obtained from original infeasibility.
The slots need not have distinct frequencies. Infinity is a separate mass.

## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
将紧化表示解紧化为有限频率和无穷远质量，定义 MomentCertificate。
-/
namespace SPR.N5.Direct

noncomputable section
open Set Polynomial

/-- At most six slots, possibly with zero weights, together with infinity mass.
The vector identity is equivalent to the six equations in
`feature_certificate_iff_moments`. Distinct-frequency merging is not assumed. -/
structure MomentCertificate (K : Box5) (b : Vec6) where
  n : ℕ
  size_le : n ≤ 6
  a : Fin n → Poly5
  t : Fin n → ℝ
  μ : Fin n → ℝ
  μinf : ℝ
  contains : ∀ i, K.Contains (a i)
  frequency_nonneg : ∀ i, 0 ≤ t i
  weight_nonneg : ∀ i, 0 ≤ μ i
  infinity_nonneg : 0 ≤ μinf
  support_size : (Finset.univ.filter (fun i => 0 < μ i)).card +
    (if 0 < μinf then 1 else 0) ≤ 6
  finite_nontrivial : ∃ i, 0 < μ i
  balance : (∑ i, μ i • feature (a i) (t i)) + μinf • infinityFeature = 0
  contacts : ∀ i, 0 < μ i → generalPairing (a i) b (t i) = 0
  infinity_contact : μinf * b 0 = 0

theorem Box5.momentCertificate_of_compact (K : Box5) (b : Vec6)
    {n : ℕ} (hn : n ≤ 6) (c : Fin n → Corner) (x w : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (hw : ∀ i, 0 < w i)
    (hsum : (∑ i, w i) = 1)
    (hz : (∑ i, w i • compactFeature (K.corner (c i)) (x i)) = 0)
    (hc : ∀ i, dot6 b (compactFeature (K.corner (c i)) (x i)) = 0) :
    Nonempty (MomentCertificate K b) := by
  obtain ⟨i, hi⟩ := certificate_has_finite_point (fun i => K.corner (c i)) x w
    (fun i => (hx i).2) hsum hz
  exact ⟨{
    n := n
    size_le := hn
    a := fun i => K.corner (c i)
    t := fun i => finiteFrequency (x i)
    μ := fun i => finiteWeight (x i) (w i)
    μinf := ∑ i, infiniteWeight (x i) (w i)
    contains := fun i => K.corner_mem (c i)
    frequency_nonneg := fun i => finiteFrequency_nonneg (hx i)
    weight_nonneg := fun i => finiteWeight_nonneg (hx i).2 (hw i).le
    infinity_nonneg := Finset.sum_nonneg fun i _ => infiniteWeight_nonneg (x i) (hw i).le
    support_size := (certificate_support_count x w).trans hn
    finite_nontrivial := ⟨i, finiteWeight_pos hi (hw i)⟩
    balance := certificate_decompactify (fun i => K.corner (c i)) x w hz
    contacts := certificate_finite_contacts (fun i => K.corner (c i)) b x w
      (fun i => (hx i).2) hc
    infinity_contact := certificate_infinity_complementarity (fun i => K.corner (c i)) b x w hc
  }⟩

/-- An original counterexample yields a stable contracted box, a nonzero weak
polynomial, and a nontrivial six-slot moment certificate. This is a necessary
condition for a counterexample, not a proof that such a counterexample exists. -/
theorem Box5.critical_moment_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ 1 ∧ (K.contract θ hθ.le).RobustlyHurwitz ∧
      ∃ b : Vec6, ‖b‖ = 1 ∧ numeratorPoly b ≠ 0 ∧ 0 ≤ b 0 ∧
        (∀ a : Poly5, (K.contract θ hθ.le).Contains a →
          ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ∧
        Nonempty (MomentCertificate (K.contract θ hθ.le) b) := by
  obtain ⟨θ, hθ, hθ1, hstable, b, hbnorm, hb0, hweak, n, hn, c, x, w,
    hx, hw, hsum, hz, hc⟩ := K.critical_six_point_certificate hK hno
  have hb : b ≠ 0 := by intro he; simp [he] at hbnorm
  exact ⟨θ, hθ, hθ1, hstable, b, hbnorm, numeratorPoly_ne_zero hb, hb0, hweak,
    (K.contract θ hθ.le).momentCertificate_of_compact b hn c x w hx hw hsum hz hc⟩

end
end SPR.N5.Direct
