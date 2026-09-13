import SPR.N5.Critical.ContractedBoxes

/-! Compact graph and the first infeasible contraction parameter.
## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
用紧性选取首次失去严格分离的参数，并保留归一化非零极限向量。
-/
namespace SPR.N5.Direct

noncomputable section
open Set Polynomial

def Box5.interpolatedFeatureSet (K : Box5) (θ : ℝ) : Set Vec6 :=
  ⋃ c : Corner, compactFeature (interpolatePoly K.lower (K.corner c) θ) '' Icc (0 : ℝ) 1

def Box5.interpolatedHull (K : Box5) (θ : ℝ) : Set Vec6 :=
  convexHull ℝ (K.interpolatedFeatureSet θ)

theorem Box5.contract_hull_eq (K : Box5) {θ : ℝ} (hθ : 0 ≤ θ) :
    (K.contract θ hθ).featureHull = K.interpolatedHull θ := by
  rw [(K.contract θ hθ).featureHull_eq_convexHull]
  unfold interpolatedHull featureSet interpolatedFeatureSet
  simp only [K.contract_corner]

def Box5.parameterGraph (K : Box5) : Set (ℝ × Vec6) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ K.interpolatedHull p.1}

def graphCombinationDomain (n : ℕ) : Set (ℝ × ((Fin n → ℝ) × (Fin n → ℝ))) :=
  Icc (0 : ℝ) 1 ×ˢ (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => Icc (0 : ℝ) 1))

def Box5.graphCombination (K : Box5) {n : ℕ} (c : Fin n → Corner)
    (p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ))) : ℝ × Vec6 :=
  (p.1, ∑ i, p.2.1 i • compactFeature (interpolatePoly K.lower (K.corner (c i)) p.1) (p.2.2 i))

theorem compact_graphCombinationDomain (n : ℕ) : IsCompact (graphCombinationDomain n) :=
  isCompact_Icc.prod ((isCompact_stdSimplex ℝ (Fin n)).prod
    (isCompact_univ_pi fun _ => isCompact_Icc))

theorem Box5.continuous_graphCombination (K : Box5) {n : ℕ} (c : Fin n → Corner) :
    Continuous (K.graphCombination c) := by
  have hg (i : Fin n) : Continuous (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      compactFeature (interpolatePoly K.lower (K.corner (c i)) p.1) (p.2.2 i)) :=
    (continuous_interpolated_feature _ _).comp
      (show Continuous (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => (p.1, p.2.2 i)) by fun_prop)
  unfold graphCombination
  apply Continuous.prodMk continuous_fst
  apply continuous_finsetSum
  intro i _
  exact (by fun_prop : Continuous (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => p.2.1 i)).smul (hg i)

theorem Box5.parameterGraph_eq_union (K : Box5) :
    K.parameterGraph = ⋃ n : Fin 8, ⋃ c : Fin n.val → Corner,
      K.graphCombination c '' graphCombinationDomain n.val := by
  apply Subset.antisymm
  · rintro ⟨θ, v⟩ ⟨hθ, hv⟩
    obtain ⟨n, hn, z, w, hz, _, hw, hsum, hcomb⟩ := finite_convex_representation hv
    have hz' : ∀ i, ∃ c : Corner, ∃ x ∈ Icc (0 : ℝ) 1,
        compactFeature (interpolatePoly K.lower (K.corner c) θ) x = z i := by
      intro i
      exact mem_iUnion.mp (hz i)
    choose c x hx heq using hz'
    refine mem_iUnion.mpr ⟨⟨n, by omega⟩, mem_iUnion.mpr ⟨c, (θ, w, x), ?_, ?_⟩⟩
    · exact ⟨hθ, ⟨fun i => (hw i).le, hsum⟩, fun i _ => hx i⟩
    · apply Prod.ext
      · rfl
      · simpa only [graphCombination, heq] using hcomb
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    obtain ⟨c, q, hq, rfl⟩ := mem_iUnion.mp hn
    refine ⟨hq.1, ?_⟩
    apply (convex_convexHull ℝ (K.interpolatedFeatureSet q.1)).sum_mem
      (fun i _ => hq.2.1.1 i) hq.2.1.2
    intro i _
    apply subset_convexHull
    exact mem_iUnion.mpr ⟨c i, q.2.2 i, hq.2.2 i (mem_univ i), rfl⟩

theorem Box5.compact_parameterGraph (K : Box5) : IsCompact K.parameterGraph := by
  rw [K.parameterGraph_eq_union]
  exact isCompact_iUnion fun n => isCompact_iUnion fun c =>
    (compact_graphCombinationDomain n.val).image (K.continuous_graphCombination c)

def Box5.zeroParameters (K : Box5) : Set ℝ :=
  {θ | θ ∈ Icc (0 : ℝ) 1 ∧ (0 : Vec6) ∈ K.interpolatedHull θ}

theorem Box5.zeroParameters_eq_image (K : Box5) :
    K.zeroParameters = Prod.fst '' (K.parameterGraph ∩ {p : ℝ × Vec6 | p.2 = 0}) := by
  ext θ
  constructor
  · intro h
    exact ⟨(θ, 0), ⟨h, rfl⟩, rfl⟩
  · rintro ⟨⟨θ', v⟩, ⟨⟨hθ, hv⟩, hz⟩, rfl⟩
    exact ⟨hθ, hz ▸ hv⟩

theorem Box5.compact_zeroParameters (K : Box5) : IsCompact K.zeroParameters := by
  rw [K.zeroParameters_eq_image]
  exact (K.compact_parameterGraph.inter_right
    (isClosed_eq continuous_snd continuous_const)).image continuous_fst

theorem Box5.exists_first_zero_parameter (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ 1 ∧ (0 : Vec6) ∈ (K.contract θ hθ.le).featureHull ∧
      ∀ σ : ℝ, ∀ hσ : 0 ≤ σ, σ < θ → (0 : Vec6) ∉ (K.contract σ hσ).featureHull := by
  have h1 : (1 : ℝ) ∈ K.zeroParameters := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    rw [← K.contract_hull_eq zero_le_one, K.contract_one_hull]
    exact K.zero_mem_of_no_synthesis hK hno
  obtain ⟨θ, hθmin⟩ := K.compact_zeroParameters.exists_isLeast ⟨1, h1⟩
  have hmem := hθmin.1
  have hθ0 : θ ≠ 0 := by
    intro hz
    have h := hmem.2
    rw [hz, ← K.contract_hull_eq le_rfl] at h
    exact K.contract_zero_separated hK h
  have hθpos : 0 < θ := lt_of_le_of_ne hmem.1.1 (Ne.symm hθ0)
  refine ⟨θ, hθpos, hmem.1.2, ?_, ?_⟩
  · rw [K.contract_hull_eq]
    exact hmem.2
  · intro σ hσ hσθ hz
    have hσmem : σ ∈ K.zeroParameters := by
      refine ⟨⟨hσ, hσθ.le.trans hmem.1.2⟩, ?_⟩
      rwa [K.contract_hull_eq] at hz
    exact (not_le_of_gt hσθ) (hθmin.2 hσmem)

end
end SPR.N5.Direct
