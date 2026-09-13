import SPR.N5.Classification.ActualCandidates

/-!
# OriginCandidates

论文 §5 与附录 A：必要候选表的完备性及基本排除。
单独处理支持包含零节点时的符号及编号，避免把边界根当作内部二重根。
-/

namespace SPR.N5.Direct
noncomputable section

namespace Classification

theorem contactSigns_origin {m : ℕ} (hm : m = 4 ∨ m = 5) (neg : Bool)
    (hinit : initialFlip (m+1) neg = false) (q : Fin (m+1) → ℕ) :
    contactSigns (m+1) neg true (List.ofFn (fun i : Fin m => q i.succ)) =
      List.ofFn (fun i : Fin (m+1) => if i = 0 then 0 else codeAt (m+1) neg q i) := by
  rcases hm with rfl | rfl <;> cases neg <;> norm_num [initialFlip] at hinit
  · exact contactSigns_five_origin q
  · exact contactSigns_six_origin q

end Classification

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem contact_signs_enumerated (C : DistinctMomentCertificate K b) {n : ℕ}
    (hn : C.nodes.card = n) {hi : ℕ} (P : CertificatePhases C hi) (hhi : hi ≤ 5)
    {c : ℝ} (hc : c ≠ 0) (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b))
    (i : Fin n) (hp : 0 < C.nodes.orderEmbOfFin hn i) :
    StageSigns (Classification.codeAt n (decide (c < 0))
      (fun j => P.phase (C.nodes.orderEmbOfFin hn j)) i)
      (evenPart (C.a (C.nodes.orderEmbOfFin hn i)) (C.nodes.orderEmbOfFin hn i))
      (oddPart (C.a (C.nodes.orderEmbOfFin hn i)) (C.nodes.orderEmbOfFin hn i)) := by
  subst n
  exact C.ordered_contact_signs P hhi hc hU hV i hp

theorem origin_initialFlip (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (hb4 : 0 < b 4) {m : ℕ} (hn : C.nodes.card = m+1)
    (hz : C.nodes.orderEmbOfFin hn 0 = 0) {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) :
    Classification.initialFlip (m+1) (decide (c < 0)) = false := by
  have hmem : (0 : ℝ) ∈ C.nodes := hz ▸ C.nodes.orderEmbOfFin_mem hn 0
  have hprod := C.zero_contact_multiplier_positive hK hb4 hU hV hmem
  have heta := ordered_nodalWeight_signed_pos (C.nodes.orderEmbOfFin hn).strictMono 0
  rw [← nodalWeight_orderEmb hn,hz] at heta
  have hh := signed_weight_product heta hc
  change (if Classification.initialFlip (m+1) (decide (c < 0)) then _ else _) at hh
  cases he : Classification.initialFlip (m+1) (decide (c < 0))
  · rfl
  · rw [he] at hh
    exact (lt_asymm hprod hh).elim

theorem actual_candidate_origin (C : DistinctMomentCertificate K b)
    (hK : K.RobustlyHurwitz) (D : RootBands K) {hi : ℕ} (P : CertificatePhases C hi)
    (hhi : hi ≤ 5) (hb4 : 0 < b 4) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (hn : C.nodes.card = m+1) (hz : C.nodes.orderEmbOfFin hn 0 = 0)
    {c : ℝ} (hc : c ≠ 0) (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) :
    Classification.Candidate hi (m+1) (decide (c < 0)) true
      (List.ofFn (fun i : Fin m => P.phase (C.nodes.orderEmbOfFin hn i.succ))) := by
  have hinit := C.origin_initialFlip hK hb4 hn hz hc hU hV
  have hmem : (0 : ℝ) ∈ C.nodes := hz ▸ C.nodes.orderEmbOfFin_mem hn 0
  have hb5 := C.zero_contact_constant hK hmem
  refine ⟨by simp [hinit],by simp,?_,?_⟩
  · apply Classification.orderedWord_ofFn _
      (P.monotone.comp ((C.nodes.orderEmbOfFin hn).monotone.comp
        (fun i j hij => Fin.succ_le_succ_iff.mpr hij)))
    · intro i
      exact P.origin_lower hb5 _ (C.nonneg _ (C.nodes.orderEmbOfFin_mem hn i.succ))
    · intro i
      exact P.upper _
  · rw [Classification.contactSigns_origin hm _ hinit
      (fun j => P.phase (C.nodes.orderEmbOfFin hn j))]
    apply Classification.zonePath_ofFn _ (fun i => D.zone (C.nodes.orderEmbOfFin hn i))
      (D.zone_monotone.comp (C.nodes.orderEmbOfFin hn).monotone)
    · intro i
      by_cases hi0 : i = 0
      · subst i
        simp only [if_pos rfl,hz]
        simp [RootBands.zone, D.ordered.1.le, Classification.zones]
      · rw [if_neg hi0]
        have hpos : 0 < C.nodes.orderEmbOfFin hn i := by
          rw [← hz]
          exact (C.nodes.orderEmbOfFin hn).strictMono (Fin.pos_iff_ne_zero.mpr hi0)
        exact D.stageSigns_zone hK (C.contains _ (C.nodes.orderEmbOfFin_mem hn i)) hpos.le
          (Classification.codeAt_lt _ (fun j => (P.upper _).trans_le hhi) i)
          (C.contact_signs_enumerated hn P hhi hc hU hV i hpos)
    · intro i
      exact Nat.zero_le _

end DistinctMomentCertificate
end
end SPR.N5.Direct
