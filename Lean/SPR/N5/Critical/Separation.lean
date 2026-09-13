import SPR.N5.Definitions.General

/-! A compact, closed-convex alternative and its implication for the original SPR goal.
The further reduction to six contact points is not assumed here.

## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
把严格公共分子的存在性归结为紧化特征向量凸包与原点的分离。
-/
namespace SPR.N5.Direct

noncomputable section
open Set Polynomial

def dot6CLM (b : Vec6) : Vec6 →L[ℝ] ℝ :=
  ∑ i : Fin 6, b i • ContinuousLinearMap.proj i

theorem dot6CLM_apply (b v : Vec6) : dot6CLM b v = dot6 b v := by
  simp [dot6CLM, dot6, ContinuousLinearMap.sum_apply]

theorem dual_eq_dot6 (f : Vec6 →L[ℝ] ℝ) (v : Vec6) :
    f v = dot6 (fun i => f (Pi.single i 1)) v := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [dot6, map_sum, map_smul, mul_comm]

def Box5.featureSet (K : Box5) : Set Vec6 :=
  ⋃ c : Corner, compactFeature (K.corner c) '' Icc (0 : ℝ) 1

def Box5.featureHull (K : Box5) : Set Vec6 := closedConvexHull ℝ K.featureSet

theorem Box5.compact_featureSet (K : Box5) : IsCompact K.featureSet := by
  exact isCompact_iUnion fun c => isCompact_Icc.image (continuous_compactFeature (K.corner c))

theorem Box5.feature_mem (K : Box5) (c : Corner) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    compactFeature (K.corner c) x ∈ K.featureSet := by
  exact mem_iUnion.mpr ⟨c, mem_image_of_mem _ hx⟩

theorem Box5.featureSet_nonempty (K : Box5) : K.featureSet.Nonempty :=
  ⟨_, K.feature_mem .D (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)⟩

/-- The four compactified corner curves all meet at infinite frequency. -/
theorem Box5.pathConnected_featureSet (K : Box5) : IsPathConnected K.featureSet := by
  have hI : IsPathConnected (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨![1, 0, 0, 0, 0, 0], ?_, ?_⟩
  · simpa only [compactFeature_at_one] using K.feature_mem .D h1
  · intro v hv
    obtain ⟨c, hc⟩ := mem_iUnion.mp hv
    have hcurve := hI.image (continuous_compactFeature (K.corner c))
    have hinf : ![1, 0, 0, 0, 0, 0] ∈ compactFeature (K.corner c) '' Icc (0 : ℝ) 1 := by
      exact ⟨1, h1, compactFeature_at_one _⟩
    exact (hcurve.joinedIn _ hinf _ hc).mono (by
      intro y hy
      exact mem_iUnion.mpr ⟨c, hy⟩)

theorem Box5.compact_featureHull (K : Box5) : IsCompact K.featureHull := by
  rw [featureHull, closedConvexHull_eq_closure_convexHull]
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (isBounded_convexHull.mpr K.compact_featureSet.isBounded).closure

theorem Box5.weak_on_hull_iff (K : Box5) (b : Vec6) :
    (∀ v ∈ K.featureHull, 0 ≤ dot6 b v) ↔ (∀ v ∈ K.featureSet, 0 ≤ dot6 b v) := by
  constructor
  · intro h v hv
    exact h v (subset_closedConvexHull hv)
  · intro h v hv
    have hsub : K.featureHull ⊆ {w | 0 ≤ dot6CLM b w} :=
      closedConvexHull_min (by simpa only [dot6CLM_apply] using h)
        (convex_halfSpace_ge (dot6CLM b).toLinearMap.isLinear 0)
        (isClosed_le continuous_const (dot6CLM b).continuous)
    simpa only [dot6CLM_apply] using hsub hv

theorem compact_positive_iff_not_mem_closedConvexHull {S : Set Vec6}
    (hS : IsCompact S) (hne : S.Nonempty) :
    (∃ b : Vec6, ∀ v ∈ S, 0 < dot6 b v) ↔ (0 : Vec6) ∉ closedConvexHull ℝ S := by
  constructor
  · rintro ⟨b, hb⟩ hzero
    obtain ⟨v, hv, hmin⟩ := hS.exists_isMinOn hne (dot6CLM b).continuous.continuousOn
    have hpos : 0 < dot6CLM b v := by simpa only [dot6CLM_apply] using hb v hv
    have hsub : closedConvexHull ℝ S ⊆ {w | dot6CLM b v ≤ dot6CLM b w} := by
      apply closedConvexHull_min
      · exact hmin
      · exact convex_halfSpace_ge (dot6CLM b).toLinearMap.isLinear (dot6CLM b v)
      · exact isClosed_le continuous_const (dot6CLM b).continuous
    have hz := hsub hzero
    simp only [mem_setOf_eq, map_zero] at hz
    exact (not_le_of_gt hpos) hz
  · intro hzero
    obtain ⟨f, u, hu, hf⟩ := geometric_hahn_banach_point_closed
      (convex_closedConvexHull (𝕜 := ℝ) (s := S)) isClosed_closedConvexHull hzero
    refine ⟨fun i => f (Pi.single i 1), ?_⟩
    intro v hv
    rw [← dual_eq_dot6]
    have := hu.trans (hf v (subset_closedConvexHull hv))
    simpa only [map_zero] using this

theorem Box5.separator_iff (K : Box5) :
    (∃ b : Vec6, 0 < b 0 ∧
      ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 < generalPairing a b t) ↔
      (0 : Vec6) ∉ K.featureHull := by
  rw [featureHull, ← compact_positive_iff_not_mem_closedConvexHull
    K.compact_featureSet K.featureSet_nonempty]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, ?_⟩
    intro v hv
    obtain ⟨c, x, hx, rfl⟩ := mem_iUnion.mp hv
    exact (compact_pairing_pos_iff _ b).mpr ⟨hb, h _ (K.corner_mem c)⟩ x hx
  · rintro ⟨b, hb⟩
    have hc (c : Corner) := (compact_pairing_pos_iff (K.corner c) b).mp
      (fun x hx => hb _ (K.feature_mem c hx))
    exact ⟨b, (hc .D).1, (K.general_pairing_pos_iff_corners b).mpr (fun c => (hc c).2)⟩

/-- A separated feature hull gives a fixed polynomial of exactly degree five. -/
theorem Box5.synthesis_of_zero_not_mem (K : Box5) (hK : K.RobustlyHurwitz)
    (hzero : (0 : Vec6) ∉ K.featureHull) :
    ∃ b : ℝ[X], b.natDegree = 5 ∧ ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b := by
  obtain ⟨b, hb, hp⟩ := K.separator_iff.mpr hzero
  exact ⟨numeratorPoly b, numeratorPoly_degree b (ne_of_gt hb),
    fun a ha => (general_frequencySPR_iff (hK a ha) b).mpr (hp a ha)⟩

/-- Original infeasibility, without an altered numerator convention, forces zero in the hull. -/
theorem Box5.zero_mem_of_no_synthesis (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    (0 : Vec6) ∈ K.featureHull := by
  by_contra hzero
  exact hno (K.synthesis_of_zero_not_mem hK hzero)

end
end SPR.N5.Direct
