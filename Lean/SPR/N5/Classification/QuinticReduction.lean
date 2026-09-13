import SPR.N5.Classification.QuarticExclusion

/-!
# QuinticReduction

论文 §5 与附录 A：必要候选表的完备性及基本排除。
基本接触限制把五次分子候选收束到 Q1–Q5，并单独排除支持含零的分支。
-/

namespace SPR.N5.Direct
noncomputable section

namespace PhaseContacts
variable {K : Box5} {b : Vec6}

/-- Every actual positive-node quintic candidate reduces to the five terminal rows.
Each discarded row is eliminated by an explicit certified contact contradiction. -/
theorem quintic_candidate_reduction {q : Fin 6 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {neg : Bool} (hcan : Classification.Candidate 5 6 neg false (List.ofFn q)) :
    neg = false ∧ (neg,false,List.ofFn q) ∈ Classification.finalFive := by
  have hrow := Classification.quintic_classification hcan
  cases neg
  · refine ⟨rfl,?_⟩
    simp only [Classification.quinticTable,List.mem_cons,List.mem_singleton,List.not_mem_nil,
      Prod.mk.injEq,Bool.false_eq_true,Bool.true_eq_false,false_and,true_and,and_true,or_false,false_or] at hrow
    rcases hrow with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18
    · have he : q = ![0,0,1,1,2,4] := List.ofFn_injective
        (h0.trans (by decide : List.ofFn ![0,0,1,1,2,4] = [0,0,1,1,2,4]).symm)
      exact (T.no_three hK hb hw 0 1 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,0,1,1,3,4] := List.ofFn_injective
        (h1.trans (by decide : List.ofFn ![0,0,1,1,3,4] = [0,0,1,1,3,4]).symm)
      exact (T.no_three hK hb hw 0 1 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,0,1,3,3,4] := List.ofFn_injective
        (h2.trans (by decide : List.ofFn ![0,0,1,3,3,4] = [0,0,1,3,3,4]).symm)
      exact (T.no_three hK hb hw 0 1 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,0,2,3,3,4] := List.ofFn_injective
        (h3.trans (by decide : List.ofFn ![0,0,2,3,3,4] = [0,0,2,3,3,4]).symm)
      exact (T.no_three hK hb hw 0 1 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,1,1,1,2,4] := List.ofFn_injective
        (h4.trans (by decide : List.ofFn ![0,1,1,1,2,4] = [0,1,1,1,2,4]).symm)
      exact (T.no_three hK hb hw 1 2 3 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,1,1,1,3,4] := List.ofFn_injective
        (h5.trans (by decide : List.ofFn ![0,1,1,1,3,4] = [0,1,1,1,3,4]).symm)
      exact (T.no_three hK hb hw 1 2 3 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,1,1,2,2,3] := List.ofFn_injective
        (h6.trans (by decide : List.ofFn ![0,1,1,2,2,3] = [0,1,1,2,2,3]).symm)
      exact (T.no_ab hK hb hb0 hw 1 2 3 4 (by decide) (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,1,1,2,2,4] := List.ofFn_injective
        (h7.trans (by decide : List.ofFn ![0,1,1,2,2,4] = [0,1,1,2,2,4]).symm)
      exact (T.no_ab hK hb hb0 hw 1 2 3 4 (by decide) (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · rw [h8]
      decide
    · have he : q = ![0,1,1,2,4,4] := List.ofFn_injective
        (h9.trans (by decide : List.ofFn ![0,1,1,2,4,4] = [0,1,1,2,4,4]).symm)
      exact (T.no_three hK hb hw 0 4 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · rw [h10]
      decide
    · have he : q = ![0,1,1,3,4,4] := List.ofFn_injective
        (h11.trans (by decide : List.ofFn ![0,1,1,3,4,4] = [0,1,1,3,4,4]).symm)
      exact (T.no_three hK hb hw 0 4 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · rw [h12]
      decide
    · have he : q = ![0,1,3,3,3,4] := List.ofFn_injective
        (h13.trans (by decide : List.ofFn ![0,1,3,3,3,4] = [0,1,3,3,3,4]).symm)
      exact (T.no_three hK hb hw 2 3 4 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,1,3,3,4,4] := List.ofFn_injective
        (h14.trans (by decide : List.ofFn ![0,1,3,3,4,4] = [0,1,3,3,4,4]).symm)
      exact (T.no_three hK hb hw 0 4 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · rw [h15]
      decide
    · have he : q = ![0,2,3,3,3,4] := List.ofFn_injective
        (h16.trans (by decide : List.ofFn ![0,2,3,3,3,4] = [0,2,3,3,3,4]).symm)
      exact (T.no_three hK hb hw 2 3 4 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · have he : q = ![0,2,3,3,4,4] := List.ofFn_injective
        (h17.trans (by decide : List.ofFn ![0,2,3,3,4,4] = [0,2,3,3,4,4]).symm)
      exact (T.no_three hK hb hw 0 4 5 (by decide) (by decide)
        (by rw [he]; rfl) (by rw [he]; rfl)).elim
    · rw [h18]
      decide
  · have hword : List.ofFn q = [1,1,2,2,3,3] := by
      simpa only [Classification.quinticTable,List.mem_cons,List.mem_singleton,List.not_mem_nil,
        Prod.mk.injEq,Bool.false_eq_true,Bool.true_eq_false,false_and,true_and,and_true,or_false,false_or] using hrow
    exact (T.exclude_112233 hK hb hb0 hw hword).elim

end PhaseContacts

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem no_quintic_origin (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (R : RootBands K) (P : CertificatePhases C 5) (hwidth : K.FullWidth)
    (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb4 : 0 < b 4)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hn : C.nodes.card = 6) {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) (hz : 0 ∈ C.nodes) : False := by
  have hcan := C.actual_candidate_origin hK R P (by decide) hb4
    (m := 5) (Or.inr rfl) hn (C.first_node_zero hn hz) hc hU hV
  have hrow := Classification.quintic_classification hcan
  have hword : List.ofFn (fun i : Fin 5 => P.phase (C.nodes.orderEmbOfFin hn i.succ)) =
      [1,2,2,3,3] := by
    simp [Classification.quinticTable] at hrow ⊢
    tauto
  exact (C.phaseContacts_tail P (by decide) hw hn).exclude_quintic_origin_12233
    hK hb0 hb1 (C.zero_contact_constant hK hz) hwidth hw hword

end DistinctMomentCertificate
end
end SPR.N5.Direct
