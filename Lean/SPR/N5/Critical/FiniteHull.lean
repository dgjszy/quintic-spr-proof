import SPR.N5.Critical.Separation

/-! Finite convex certificates and compactness of ordinary convex hulls in R^6.
## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
有限凸表示、闭性和紧性的辅助结论；供临界参数和支持点约化使用。
-/
namespace SPR.N5.Direct

noncomputable section
open Set Polynomial

theorem affineIndependent_card_le_seven {ι : Type*} [Fintype ι] {z : ι → Vec6}
    (hz : AffineIndependent ℝ z) : Fintype.card ι ≤ 7 := by
  have hcard := hz.card_le_finrank_succ
  have hdim : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ 6 := by
    simpa [Vec6] using Submodule.finrank_le (vectorSpan ℝ (Set.range z))
  omega

/-- Positive Caratheodory representation, reindexed by Fin n for subsequent compactness. -/
theorem finite_convex_representation {S : Set Vec6} {x : Vec6}
    (hx : x ∈ convexHull ℝ S) :
    ∃ n : ℕ, n ≤ 7 ∧ ∃ (z : Fin n → Vec6) (w : Fin n → ℝ),
      (∀ i, z i ∈ S) ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • z i) = x := by
  obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, affineIndependent_card_le_seven hind, z ∘ e, w ∘ e,
    (fun i => hz ⟨e i, rfl⟩), hind.comp_embedding e.toEmbedding, (fun i => hw (e i)), ?_, ?_⟩
  · exact (e.sum_comp w).trans hsum
  · exact (e.sum_comp (fun i => w i • z i)).trans hcomb

def combinationMap (n : ℕ) (p : (Fin n → ℝ) × (Fin n → Vec6)) : Vec6 :=
  ∑ i, p.1 i • p.2 i

def combinationDomain (n : ℕ) (S : Set Vec6) : Set ((Fin n → ℝ) × (Fin n → Vec6)) :=
  stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => S)

def combinationImage (n : ℕ) (S : Set Vec6) : Set Vec6 :=
  combinationMap n '' combinationDomain n S

theorem compact_combinationImage (n : ℕ) {S : Set Vec6} (hS : IsCompact S) :
    IsCompact (combinationImage n S) := by
  have hd : IsCompact (combinationDomain n S) :=
    (isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hS)
  exact hd.image (by unfold combinationMap; fun_prop)

theorem combinationImage_subset_convexHull (n : ℕ) (S : Set Vec6) :
    combinationImage n S ⊆ convexHull ℝ S := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ S (hz i (mem_univ i)))

theorem convexHull_eq_finite_union (S : Set Vec6) :
    convexHull ℝ S = ⋃ n : Fin 8, combinationImage n.val S := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨n, hn, z, w, hz, _, hw, hsum, hcomb⟩ := finite_convex_representation hx
    refine mem_iUnion.mpr ⟨⟨n, by omega⟩, (w, z), ?_, hcomb⟩
    exact ⟨⟨fun i => (hw i).le, hsum⟩, fun i _ => hz i⟩
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact combinationImage_subset_convexHull n.val S hn

theorem compact_convexHull_six {S : Set Vec6} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rw [convexHull_eq_finite_union]
  exact isCompact_iUnion fun n => compact_combinationImage n.val hS

theorem closedConvexHull_eq_convexHull_six {S : Set Vec6} (hS : IsCompact S) :
    closedConvexHull ℝ S = convexHull ℝ S := by
  rw [closedConvexHull_eq_closure_convexHull, (compact_convexHull_six hS).isClosed.closure_eq]

theorem Box5.featureHull_eq_convexHull (K : Box5) :
    K.featureHull = convexHull ℝ K.featureSet :=
  closedConvexHull_eq_convexHull_six K.compact_featureSet

/-- Actual original infeasibility gives a finite positive certificate, including
infinite-frequency features. Six-point sharpening requires support information. -/
theorem Box5.seven_point_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ n : ℕ, n ≤ 7 ∧ ∃ (z : Fin n → Vec6) (w : Fin n → ℝ),
      (∀ i, z i ∈ K.featureSet) ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • z i) = 0 := by
  apply finite_convex_representation
  rw [← K.featureHull_eq_convexHull]
  exact K.zero_mem_of_no_synthesis hK hno

end
end SPR.N5.Direct
