import SPR.N5.Classification.BasicWordExclusions

/-!
# QuarticExclusion

论文 §5 与附录 A：必要候选表的完备性及基本排除。
分别排除五个有限节点加无穷远、以及六个有限节点的四次分子情形。
-/

namespace SPR.N5.Direct
noncomputable section

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem first_node_zero (C : DistinctMomentCertificate K b) {m : ℕ}
    (hn : C.nodes.card = m+1) (hz : 0 ∈ C.nodes) : C.nodes.orderEmbOfFin hn 0 = 0 := by
  let j := (C.nodes.orderIsoOfFin hn).symm ⟨0,hz⟩
  have hj : C.nodes.orderEmbOfFin hn j = 0 := by
    exact congrArg Subtype.val ((C.nodes.orderIsoOfFin hn).apply_symm_apply ⟨0,hz⟩)
  exact le_antisymm (((C.nodes.orderEmbOfFin hn).monotone (Fin.zero_le j)).trans_eq hj)
    (C.nonneg _ (C.nodes.orderEmbOfFin_mem hn 0))

theorem positive_nodes_of_no_zero (C : DistinctMomentCertificate K b) (hz : 0 ∉ C.nodes) :
    ∀ r ∈ C.nodes, 0 < r := by
  intro r hr
  exact lt_of_le_of_ne (C.nonneg r hr) (fun he => hz (he ▸ hr))

theorem candidate_no_origin_enumerated (C : DistinctMomentCertificate K b)
    (hK : K.RobustlyHurwitz) (D : RootBands K) {hi : ℕ} (P : CertificatePhases C hi)
    (hhi : hi ≤ 5) {n : ℕ} (hn : C.nodes.card = n) (hn56 : n = 5 ∨ n = 6)
    (hp : ∀ r ∈ C.nodes, 0 < r) {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) :
    Classification.Candidate hi n (decide (c < 0)) false
      (List.ofFn (fun i => P.phase (C.nodes.orderEmbOfFin hn i))) := by
  subst n
  exact C.actual_candidate_no_origin hK D P hhi hn56 hp hc hU hV

/-- Actual five-finite-node certificates with infinity are impossible. -/
theorem no_five_nodes (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (D : RootBands K) (P : CertificatePhases C 4) (hb : b ≠ 0) (hb0 : b 0 = 0)
    (hb4 : 0 < b 4)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hn : C.nodes.card = 5) {c : ℝ} (hc : 0 < c)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) : False := by
  have hneg : decide (c < 0) = false := by simp [not_lt_of_ge hc.le]
  have hb0n : 0 ≤ b 0 := by rw [hb0]
  by_cases hz : 0 ∈ C.nodes
  · have hcan := C.actual_candidate_origin hK D P (by decide) hb4
      (m := 4) (Or.inl rfl) hn (C.first_node_zero hn hz) (ne_of_gt hc) hU hV
    rw [hneg] at hcan
    have hrow := Classification.infinity_classification hcan
    simp only [Classification.infinityTable,List.mem_cons,List.mem_singleton,
      Prod.mk.injEq,Bool.false_eq_true, false_and, or_false, false_or, true_and] at hrow
    exact (C.phaseContacts_tail P (by decide) hw hn).exclude_quartic_origin_1223
      hK hb hb0 (C.zero_contact_constant hK hz) hw (by simpa using hrow)
  · have hp := C.positive_nodes_of_no_zero hz
    have hcan := C.candidate_no_origin_enumerated hK D P (by decide) hn
      (Or.inl rfl) hp (ne_of_gt hc) hU hV
    rw [hneg] at hcan
    have hrow := Classification.infinity_classification hcan
    simp only [Classification.infinityTable,List.mem_cons,List.mem_singleton,
      Prod.mk.injEq,Bool.false_eq_true, false_and, or_false, false_or, true_and] at hrow
    exact (C.phaseContacts P (by decide) hw hn hp).exclude_11223 hK hb hb0n hw
      (by simpa using hrow)

/-- Actual six-finite-node certificates with quartic numerator are impossible. -/
theorem no_quartic_six_nodes (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (D : RootBands K) (P : CertificatePhases C 4) (hb : b ≠ 0) (hb0 : b 0 = 0)
    (hb4 : 0 < b 4)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hn : C.nodes.card = 6) {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) : False := by
  have hb0n : 0 ≤ b 0 := by rw [hb0]
  by_cases hz : 0 ∈ C.nodes
  · have hcan := C.actual_candidate_origin hK D P (by decide) hb4
      (m := 5) (Or.inr rfl) hn (C.first_node_zero hn hz) hc hU hV
    have hrow := Classification.quartic_classification hcan
    have hword : List.ofFn (fun i : Fin 5 => P.phase (C.nodes.orderEmbOfFin hn i.succ)) =
        [1,2,2,3,3] := by
      simp [Classification.quarticTable] at hrow ⊢
      tauto
    exact (C.phaseContacts_tail P (by decide) hw hn).exclude_quartic_origin_12233
      hK hb hb0 (C.zero_contact_constant hK hz) hw hword
  · have hp := C.positive_nodes_of_no_zero hz
    have hcan := C.candidate_no_origin_enumerated hK D P (by decide) hn
      (Or.inr rfl) hp hc hU hV
    have hrow := Classification.quartic_classification hcan
    have hword : List.ofFn (fun i : Fin 6 => P.phase (C.nodes.orderEmbOfFin hn i)) = [0,1,1,2,2,3] ∨
        List.ofFn (fun i : Fin 6 => P.phase (C.nodes.orderEmbOfFin hn i)) = [1,1,2,2,3,3] := by
      simp [Classification.quarticTable] at hrow ⊢
      tauto
    rcases hword with hword | hword
    · exact (C.phaseContacts P (by decide) hw hn hp).exclude_011223 hK hb hb0n hw hword
    · exact (C.phaseContacts P (by decide) hw hn hp).exclude_112233 hK hb hb0n hw hword

end DistinctMomentCertificate
end
end SPR.N5.Direct
