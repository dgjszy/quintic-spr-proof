import SPR.N5.Critical.CriticalParameter

/-! Normalized separator limits produce a nonzero weak support at the first
infeasible contraction. This avoids a set-valued interior-continuity assumption.

## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
从临界参数提取非负分子及接触支持，保留无穷远端点。
-/
namespace SPR.N5.Direct

noncomputable section
open Set Filter Polynomial
open scoped Topology

def approachBelow (θ : ℝ) (n : ℕ) : ℝ := θ * (1 - 1 / ((n : ℝ) + 1))

theorem approachBelow_bounds {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    0 ≤ approachBelow θ n ∧ approachBelow θ n < θ := by
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hi : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one hd).mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  have hip : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hd
  refine ⟨mul_nonneg hθ.le (sub_nonneg.mpr hi), ?_⟩
  unfold approachBelow
  nlinarith [mul_pos hθ hip]

theorem approachBelow_tendsto (θ : ℝ) : Tendsto (approachBelow θ) atTop (𝓝 θ) := by
  change Tendsto (fun n : ℕ => θ * (1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 θ)
  simpa only [sub_zero, mul_one] using (tendsto_const_nhds (x := θ)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat)

theorem dot6_smul_left (b v : Vec6) (r : ℝ) : dot6 (r • b) v = r * dot6 b v := by
  simp only [dot6, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem continuous_dot6 : Continuous (fun p : Vec6 × Vec6 => dot6 p.1 p.2) := by
  unfold dot6
  fun_prop

theorem numeratorPoly_coeff_descending (b : Vec6) (i : Fin 6) :
    (numeratorPoly b).coeff (5 - i.val) = b i := by
  fin_cases i <;> norm_num only [numeratorPoly, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_C, Fin.val_zero, Fin.val_one, Nat.reduceSub,
    ite_false, ite_true, add_zero, zero_add] <;> rfl

theorem numeratorPoly_ne_zero {b : Vec6} (hb : b ≠ 0) : numeratorPoly b ≠ 0 := by
  intro h
  apply hb
  funext i
  have he := congrArg (fun p : ℝ[X] => p.coeff (5 - i.val)) h
  dsimp only at he
  rw [numeratorPoly_coeff_descending, coeff_zero] at he
  exact he

theorem Box5.limit_support_at_first (K : Box5) {θ : ℝ} (hθ : 0 < θ)
    (hbefore : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ, σ < θ → (0 : Vec6) ∉ (K.contract σ hσ).featureHull) :
    ∃ b : Vec6, ‖b‖ = 1 ∧ 0 ≤ b 0 ∧
      ∀ a : Poly5, (K.contract θ hθ.le).Contains a →
        ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t := by
  have hsep (n : ℕ) :=
    (K.contract (approachBelow θ n) (approachBelow_bounds hθ n).1).separator_iff.mpr
    (hbefore _ (approachBelow_bounds hθ n).1 (approachBelow_bounds hθ n).2)
  choose b hb0 hpair using hsep
  have hbne (n : ℕ) : b n ≠ 0 := by
    intro hzero
    have h := hb0 n
    simp only [hzero, Pi.zero_apply, lt_self_iff_false] at h
  let v : ℕ → Vec6 := fun n => (‖b n‖⁻¹ : ℝ) • b n
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := norm_smul_inv_norm (hbne n)
  obtain ⟨b', hb', φ, hφ, hlim⟩ := (isCompact_sphere (0 : Vec6) 1).tendsto_subseq
    (fun n => (show v n ∈ Metric.sphere (0 : Vec6) 1 by simpa using hvnorm n))
  have hb'norm : ‖b'‖ = 1 := by simpa using hb'
  have hσlim : Tendsto (fun n => approachBelow θ (φ n)) atTop (𝓝 θ) :=
    (approachBelow_tendsto θ).comp hφ.tendsto_atTop
  have hcorner (c : Corner) : ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ dot6 b' (compactFeature ((K.contract θ hθ.le).corner c) x) := by
    intro x hx
    have hinput : Tendsto (fun n => (approachBelow θ (φ n), x)) atTop (𝓝 (θ, x)) :=
      hσlim.prodMk_nhds tendsto_const_nhds
    have hg0 := Filter.Tendsto.comp
      ((continuous_interpolated_feature K.lower (K.corner c)).tendsto (θ, x)) hinput
    have hg : Tendsto (fun n => compactFeature
        (interpolatePoly K.lower (K.corner c) (approachBelow θ (φ n))) x) atTop
        (𝓝 (compactFeature (interpolatePoly K.lower (K.corner c) θ) x)) := hg0
    have hd := (continuous_dot6.tendsto
      (b', compactFeature (interpolatePoly K.lower (K.corner c) θ) x)).comp
        (hlim.prodMk_nhds hg)
    rw [K.contract_corner]
    apply ge_of_tendsto hd
    apply Eventually.of_forall
    intro n
    change 0 ≤ dot6 (v (φ n)) (compactFeature
      (interpolatePoly K.lower (K.corner c) (approachBelow θ (φ n))) x)
    dsimp only [v]
    rw [dot6_smul_left]
    apply mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    have hc := (compact_pairing_pos_iff
      ((K.contract (approachBelow θ (φ n)) (approachBelow_bounds hθ (φ n)).1).corner c)
      (b (φ n))).mpr ⟨hb0 (φ n), hpair (φ n) _
        ((K.contract (approachBelow θ (φ n)) (approachBelow_bounds hθ (φ n)).1).corner_mem c)⟩ x hx
    rw [K.contract_corner] at hc
    exact hc.le
  have hc (c : Corner) := (compact_pairing_nonneg_iff _ b').mp (hcorner c)
  exact ⟨b', hb'norm, (hc .D).1,
    ((K.contract θ hθ.le).general_pairing_nonneg_iff_corners b').mpr (fun c => (hc c).2)⟩

/-- From an actual counterexample to a stable contracted box with a normalized
weak numerator and at most six positive compact contact weights. The original
box may be degenerate; full-dimensional widening is supplied by Stability.StableExpansion and Convex.FullWidthCritical. -/
theorem Box5.critical_six_point_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ 1 ∧ (K.contract θ hθ.le).RobustlyHurwitz ∧
      ∃ b : Vec6, ‖b‖ = 1 ∧ 0 ≤ b 0 ∧
        (∀ a : Poly5, (K.contract θ hθ.le).Contains a →
          ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ∧
        ∃ n : ℕ, n ≤ 6 ∧ ∃ (c : Fin n → Corner) (x w : Fin n → ℝ),
          (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
            (∑ i, w i • compactFeature ((K.contract θ hθ.le).corner (c i)) (x i)) = 0 ∧
            ∀ i, dot6 b (compactFeature ((K.contract θ hθ.le).corner (c i)) (x i)) = 0 := by
  obtain ⟨θ, hθ, hθ1, hzero, hbefore⟩ := K.exists_first_zero_parameter hK hno
  obtain ⟨b, hbnorm, hb0, hweak⟩ := K.limit_support_at_first hθ hbefore
  have hb : b ≠ 0 := by intro hz; simp [hz] at hbnorm
  exact ⟨θ, hθ, hθ1, K.contract_hurwitz hK hθ.le hθ1, b, hbnorm, hb0, hweak,
    (K.contract θ hθ.le).supported_six_point_certificate hzero b hb hb0 hweak⟩

end
end SPR.N5.Direct
