import SPR.N5.Interpolation.InterpolationSigns

/-!
# OrderedWeights

论文 §4.3：消失矩、插值恒等式及支持点个数。
按递增节点编号，证明插值权重的交替符号并供分类编码使用。
-/

namespace SPR.N5.Direct
noncomputable section
open Finset

/-- Alternating signs of Lagrange nodal weights on strictly increasing nodes. -/
theorem ordered_nodalWeight_signed_pos {n : ℕ} {t : Fin n → ℝ} (ht : StrictMono t) (i : Fin n) :
    0 < (-1 : ℝ)^(n-1-i.val) * Lagrange.nodalWeight univ t i := by
  have he : ((univ.erase i).filter (fun j : Fin n => i < j)) = Ioi i := by
    ext j
    simp only [mem_filter,mem_erase,mem_univ,and_true,mem_Ioi]
    exact ⟨fun h => h.2,fun h => ⟨ne_of_gt h,h⟩⟩
  have hs : (∏ j ∈ univ.erase i, (if i < j then (-1 : ℝ) else 1)) =
      (-1 : ℝ)^(n-1-i.val) := by
    rw [prod_ite]
    simp [he,Fin.card_Ioi]
  have hp : 0 < ∏ j ∈ univ.erase i,
      (if i < j then (-1 : ℝ) else 1) * (t i-t j)⁻¹ := by
    apply prod_pos
    intro j hj
    by_cases hij : i < j
    · rw [if_pos hij]
      have hn : (t i-t j)⁻¹ < 0 := inv_lt_zero.mpr (sub_neg.mpr (ht hij))
      linarith
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (mem_erase.mp hj).1
      rw [if_neg hij,one_mul]
      exact inv_pos.mpr (sub_pos.mpr (ht hji))
  simpa only [prod_mul_distrib,hs,Lagrange.nodalWeight] using hp

/-- Nodal weights are unchanged by increasing enumeration of a finite set. -/
theorem nodalWeight_orderEmb {s : Finset ℝ} {n : ℕ} (hn : s.card = n) (i : Fin n) :
    Lagrange.nodalWeight s id (s.orderEmbOfFin hn i) =
      Lagrange.nodalWeight univ (s.orderEmbOfFin hn) i := by
  classical
  let e := s.orderEmbOfFin hn
  have he : (univ.erase i).image e = s.erase (e i) := by
    rw [image_erase e.injective,Finset.image_orderEmbOfFin_univ]
  simp only [Lagrange.nodalWeight,id_eq]
  rw [← he,prod_image]
  exact e.injective.injOn

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

def orderedNode (C : DistinctMomentCertificate K b) : Fin C.nodes.card ↪o ℝ :=
  C.nodes.orderEmbOfFin rfl

theorem orderedNode_mem (C : DistinctMomentCertificate K b) (i : Fin C.nodes.card) :
    C.orderedNode i ∈ C.nodes := C.nodes.orderEmbOfFin_mem rfl i

theorem orderedNode_weight_sign (C : DistinctMomentCertificate K b) (i : Fin C.nodes.card) :
    0 < (-1 : ℝ)^(C.nodes.card-1-i.val) *
      Lagrange.nodalWeight C.nodes id (C.orderedNode i) := by
  rw [orderedNode,nodalWeight_orderEmb]
  exact ordered_nodalWeight_signed_pos (C.nodes.orderEmbOfFin rfl).strictMono i

end DistinctMomentCertificate
end
end SPR.N5.Direct
