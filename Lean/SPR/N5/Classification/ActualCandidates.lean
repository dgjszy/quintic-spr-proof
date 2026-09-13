import SPR.N5.Contacts.PhaseCertificate

/-!
# ActualCandidates

论文 §5 与附录 A：必要候选表的完备性及基本排除。
证明无零节点的真实接触数据满足候选条件；这是有限枚举的应用桥接。
-/

namespace SPR.N5.Direct
noncomputable section

namespace Classification

theorem contactSigns_no_origin {n : ℕ} (hn : n = 5 ∨ n = 6) (neg : Bool) (q : Fin n → ℕ) :
    contactSigns n neg false (List.ofFn q) = List.ofFn (codeAt n neg q) := by
  rcases hn with rfl | rfl <;> cases neg <;>
    simp only [List.ofFn_succ,List.ofFn_zero] <;> rfl

theorem contactSigns_six_origin (q : Fin 6 → ℕ) :
    contactSigns 6 true true (List.ofFn (fun i : Fin 5 => q i.succ)) =
      List.ofFn (fun i : Fin 6 => if i = 0 then 0 else codeAt 6 true q i) := by
  simp only [List.ofFn_succ,List.ofFn_zero]
  rfl

theorem contactSigns_five_origin (q : Fin 5 → ℕ) :
    contactSigns 5 false true (List.ofFn (fun i : Fin 4 => q i.succ)) =
      List.ofFn (fun i : Fin 5 => if i = 0 then 0 else codeAt 5 false q i) := by
  simp only [List.ofFn_succ,List.ofFn_zero]
  rfl

end Classification

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem actual_candidate_no_origin (C : DistinctMomentCertificate K b)
    (hK : K.RobustlyHurwitz) (D : RootBands K) {hi : ℕ} (P : CertificatePhases C hi)
    (hhi : hi ≤ 5) (hn : C.nodes.card = 5 ∨ C.nodes.card = 6)
    (hpositive : ∀ r ∈ C.nodes, 0 < r) {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) :
    Classification.Candidate hi C.nodes.card (decide (c < 0)) false
      (List.ofFn (fun i => P.phase (C.orderedNode i))) := by
  refine ⟨by simp,by simp,?_,?_⟩
  · exact Classification.orderedWord_ofFn _ (P.monotone.comp C.orderedNode.monotone)
      (fun i => Nat.zero_le _) (fun i => P.upper _)
  · rw [Classification.contactSigns_no_origin hn]
    apply Classification.zonePath_ofFn _ (fun i => D.zone (C.orderedNode i))
      (D.zone_monotone.comp C.orderedNode.monotone)
    · intro i
      exact D.stageSigns_zone hK (C.contains _ (C.orderedNode_mem i))
        (C.nonneg _ (C.orderedNode_mem i))
        (Classification.codeAt_lt _ (fun j => (P.upper _).trans_le hhi) i)
        (C.ordered_contact_signs P hhi hc hU hV i (hpositive _ (C.orderedNode_mem i)))
    · intro i
      exact Nat.zero_le _

end DistinctMomentCertificate
end
end SPR.N5.Direct
