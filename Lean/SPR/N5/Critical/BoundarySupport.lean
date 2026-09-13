import SPR.N5.Critical.SupportedCertificate

/-! Support at zero, including convex sets with empty ambient interior.
## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
处理临界凸集的支撑向量，包括凸集在环境空间中内点为空的情形。
-/
namespace SPR.N5.Direct

noncomputable section
open Set

theorem nonzero_support_of_not_interior {C : Set Vec6} (hC : Convex ℝ C)
    (hz : (0 : Vec6) ∈ C) (hboundary : (0 : Vec6) ∉ interior C) :
    ∃ f : Vec6 →L[ℝ] ℝ, f ≠ 0 ∧ ∀ x ∈ C, 0 ≤ f x := by
  by_cases hint : (interior C).Nonempty
  · obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hC hboundary hint
    refine ⟨-f, neg_ne_zero.mpr hf, ?_⟩
    intro x hx
    have h := hmax x hx
    simpa only [ContinuousLinearMap.neg_apply, neg_nonneg, map_zero] using h
  · have haff : affineSpan ℝ C ≠ ⊤ := by
      intro h
      exact hint (hC.interior_nonempty_iff_affineSpan_eq_top.mpr h)
    have hspanEq : (affineSpan ℝ C : Set Vec6) = (Submodule.span ℝ C : Set Vec6) := by
      simpa only [insert_eq_of_mem hz] using affineSpan_insert_zero (k := ℝ) C
    have hspan : Submodule.span ℝ C ≠ ⊤ := by
      intro h
      apply haff
      apply SetLike.coe_injective
      rw [hspanEq, h]
      rfl
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr hspan) inferInstance
    refine ⟨f.toContinuousLinearMap, ?_, ?_⟩
    · intro h
      apply hf
      apply LinearMap.ext
      intro x
      exact congrArg (fun g : Vec6 →L[ℝ] ℝ => g x) h
    · intro x hx
      have hm : f x ∈ (Submodule.span ℝ C).map f := ⟨x, Submodule.subset_span hx, rfl⟩
      rw [hmap] at hm
      have heq : f x = 0 := by simpa using hm
      exact heq.ge

/-- Boundary information gives both a nonzero supporting functional and a
positive certificate with at most six points. No full-dimensionality assumption
is used in this convex-geometric theorem. -/
theorem boundary_six_point_representation {S : Set Vec6} (hS : IsCompact S)
    (hzero : (0 : Vec6) ∈ closedConvexHull ℝ S)
    (hboundary : (0 : Vec6) ∉ interior (closedConvexHull ℝ S)) :
    ∃ f : Vec6 →L[ℝ] ℝ, f ≠ 0 ∧ (∀ z ∈ S, 0 ≤ f z) ∧
      ∃ n : ℕ, n ≤ 6 ∧ ∃ (z : Fin n → Vec6) (w : Fin n → ℝ),
        (∀ i, z i ∈ S) ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
          (∑ i, w i) = 1 ∧ (∑ i, w i • z i) = 0 ∧ ∀ i, f (z i) = 0 := by
  obtain ⟨f, hf, hpos⟩ := nonzero_support_of_not_interior convex_closedConvexHull hzero hboundary
  have hSpos : ∀ z ∈ S, 0 ≤ f z := fun z hz => hpos z (subset_closedConvexHull hz)
  exact ⟨f, hf, hSpos, supported_six_point_representation hS hzero f hf hSpos⟩

theorem Box5.boundary_weak_support (K : Box5) (hzero : (0 : Vec6) ∈ K.featureHull)
    (hboundary : (0 : Vec6) ∉ interior K.featureHull) :
    ∃ b : Vec6, b ≠ 0 ∧ 0 ≤ b 0 ∧
      ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t := by
  obtain ⟨f, hf, hpos⟩ := nonzero_support_of_not_interior convex_closedConvexHull hzero hboundary
  let b : Vec6 := fun i => f (Pi.single i 1)
  have hb : b ≠ 0 := by
    intro hb0
    apply hf
    apply ContinuousLinearMap.ext
    intro v
    rw [dual_eq_dot6]
    change dot6 b v = 0
    simp [hb0, dot6]
  have hc (c : Corner) : 0 ≤ b 0 ∧
      ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing (K.corner c) b t := by
    apply (compact_pairing_nonneg_iff _ b).mp
    intro x hx
    rw [← dual_eq_dot6]
    exact hpos _ (subset_closedConvexHull (K.feature_mem c hx))
  exact ⟨b, hb, (hc .D).1,
    (K.general_pairing_nonneg_iff_corners b).mpr (fun c => (hc c).2)⟩

theorem Box5.boundary_six_point_certificate (K : Box5) (hzero : (0 : Vec6) ∈ K.featureHull)
    (hboundary : (0 : Vec6) ∉ interior K.featureHull) :
    ∃ b : Vec6, b ≠ 0 ∧ 0 ≤ b 0 ∧
      (∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ∧
      ∃ n : ℕ, n ≤ 6 ∧ ∃ (c : Fin n → Corner) (x w : Fin n → ℝ),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
          (∑ i, w i • compactFeature (K.corner (c i)) (x i)) = 0 ∧
          ∀ i, dot6 b (compactFeature (K.corner (c i)) (x i)) = 0 := by
  obtain ⟨b, hb, hb0, hweak⟩ := K.boundary_weak_support hzero hboundary
  exact ⟨b, hb, hb0, hweak, K.supported_six_point_certificate hzero b hb hb0 hweak⟩

end
end SPR.N5.Direct
