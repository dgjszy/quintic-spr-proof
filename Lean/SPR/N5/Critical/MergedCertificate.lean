import SPR.N5.Critical.CoefficientAverages

/-!
# MergedCertificate

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
合并相同频率并去除零权重，得到互异节点、正权重及同一个支持界。
-/

namespace SPR.N5.Direct
noncomputable section
open Finset

namespace MomentCertificate
variable {K : Box5} {b : Vec6}

def active (C : MomentCertificate K b) : Finset (Fin C.n) :=
  univ.filter (fun i => 0 < C.μ i)
def nodes (C : MomentCertificate K b) : Finset ℝ := C.active.image C.t
def fiber (C : MomentCertificate K b) (r : ℝ) : Finset (Fin C.n) :=
  C.active.filter (fun i => C.t i = r)
def mergedWeight (C : MomentCertificate K b) (r : ℝ) : ℝ := ∑ i ∈ C.fiber r, C.μ i
def mergedDenominator (C : MomentCertificate K b) (r : ℝ) : Poly5 :=
  averagePoly (C.fiber r) C.μ C.a

theorem nodes_nonempty (C : MomentCertificate K b) : C.nodes.Nonempty := by
  obtain ⟨i,hi⟩ := C.finite_nontrivial
  exact ⟨C.t i, mem_image.mpr ⟨i, by simp [active,hi], rfl⟩⟩

theorem nodes_support_bound (C : MomentCertificate K b) :
    C.nodes.card + (if 0 < C.μinf then 1 else 0) ≤ 6 :=
  (Nat.add_le_add_right card_image_le _).trans C.support_size

theorem node_nonneg (C : MomentCertificate K b) {r : ℝ} (hr : r ∈ C.nodes) : 0 ≤ r := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
  exact C.frequency_nonneg i

theorem fiber_nonempty (C : MomentCertificate K b) {r : ℝ} (hr : r ∈ C.nodes) :
    (C.fiber r).Nonempty := by
  obtain ⟨i,hi,hir⟩ := mem_image.mp hr
  exact ⟨i,mem_filter.mpr ⟨hi,hir⟩⟩

theorem mergedWeight_pos (C : MomentCertificate K b) {r : ℝ} (hr : r ∈ C.nodes) :
    0 < C.mergedWeight r := by
  apply sum_pos
  · intro i hi
    exact (mem_filter.mp (mem_filter.mp hi).1).2
  · exact C.fiber_nonempty hr

theorem mergedDenominator_mem (C : MomentCertificate K b) {r : ℝ} (hr : r ∈ C.nodes) :
    K.Contains (C.mergedDenominator r) :=
  K.averagePoly_mem _ _ _ (fun i _ => C.weight_nonneg i) (C.mergedWeight_pos hr)
    (fun i _ => C.contains i)

theorem merged_contact (C : MomentCertificate K b) {r : ℝ} (hr : r ∈ C.nodes) :
    generalPairing (C.mergedDenominator r) b r = 0 := by
  apply averagePoly_contact _ _ _ _ _ (ne_of_gt (C.mergedWeight_pos hr))
  intro i hi
  obtain ⟨hi,htr⟩ := mem_filter.mp hi
  rw [← htr]
  exact C.contacts i (mem_filter.mp hi).2

theorem merged_feature (C : MomentCertificate K b) {r : ℝ} (hr : r ∈ C.nodes) :
    C.mergedWeight r • feature (C.mergedDenominator r) r =
      ∑ i ∈ C.fiber r, C.μ i • feature (C.a i) (C.t i) := by
  rw [mergedWeight, mergedDenominator,
    averagePoly_feature _ _ _ _ (ne_of_gt (C.mergedWeight_pos hr))]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

theorem merged_balance (C : MomentCertificate K b) :
    (∑ r ∈ C.nodes, C.mergedWeight r • feature (C.mergedDenominator r) r) +
      C.μinf • infinityFeature = 0 := by
  have he : (∑ r ∈ C.nodes, C.mergedWeight r • feature (C.mergedDenominator r) r) =
      ∑ i, C.μ i • feature (C.a i) (C.t i) := by
    calc
      _ = ∑ r ∈ C.nodes, ∑ i ∈ C.fiber r, C.μ i • feature (C.a i) (C.t i) :=
        sum_congr rfl (fun r hr => C.merged_feature hr)
      _ = ∑ i ∈ C.active, C.μ i • feature (C.a i) (C.t i) :=
        sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem C.t hi) _
      _ = _ := by
        apply sum_subset (filter_subset _ _)
        intro i hi hia
        have hz : C.μ i = 0 := le_antisymm (le_of_not_gt (by simpa [active] using hia))
          (C.weight_nonneg i)
        simp [hz]
  rw [he]
  exact C.balance

end MomentCertificate

/-- A certificate with genuinely distinct finite frequencies and positive weights.
Infinity is retained as a separate mass and counts toward the six-point bound. -/
structure DistinctMomentCertificate (K : Box5) (b : Vec6) where
  nodes : Finset ℝ
  a : ℝ → Poly5
  μ : ℝ → ℝ
  μinf : ℝ
  nonempty : nodes.Nonempty
  size : nodes.card + (if 0 < μinf then 1 else 0) ≤ 6
  contains : ∀ r ∈ nodes, K.Contains (a r)
  nonneg : ∀ r ∈ nodes, 0 ≤ r
  positive : ∀ r ∈ nodes, 0 < μ r
  infinity_nonneg : 0 ≤ μinf
  balance : (∑ r ∈ nodes, μ r • feature (a r) r) + μinf • infinityFeature = 0
  contacts : ∀ r ∈ nodes, generalPairing (a r) b r = 0
  infinity_contact : μinf * b 0 = 0

def MomentCertificate.merge {K : Box5} {b : Vec6} (C : MomentCertificate K b) :
    DistinctMomentCertificate K b where
  nodes := C.nodes
  a := C.mergedDenominator
  μ := C.mergedWeight
  μinf := C.μinf
  nonempty := C.nodes_nonempty
  size := C.nodes_support_bound
  contains := fun _ hr => C.mergedDenominator_mem hr
  nonneg := fun _ hr => C.node_nonneg hr
  positive := fun _ hr => C.mergedWeight_pos hr
  infinity_nonneg := C.infinity_nonneg
  balance := C.merged_balance
  contacts := fun _ hr => C.merged_contact hr
  infinity_contact := C.infinity_contact

end
end SPR.N5.Direct
