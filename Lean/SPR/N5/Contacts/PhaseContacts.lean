import SPR.N5.Classification.OriginCandidates
import SPR.N5.Contacts.StableContacts

/-!
# PhaseContacts

论文 §5：接触点重数、符号和极小顶点之间的联系。
将真实正接触按分子区间编号组织，使基本重数排除可逐行应用。
-/

namespace SPR.N5.Direct
noncomputable section

/-- Strictly ordered positive corner contacts, indexed by their numerator phases. -/
structure PhaseContacts (K : Box5) (b : Vec6) {n : ℕ} (q : Fin n → ℕ) where
  t : Fin n → ℝ
  positive : ∀ i, 0 < t i
  increasing : StrictMono t
  contacts : ∀ i, generalPairing (K.corner (phaseCorner (q i))) b (t i) = 0

namespace PhaseContacts
variable {K : Box5} {b : Vec6} {n : ℕ} {q : Fin n → ℕ}

theorem no_three (T : PhaseContacts K b q) (hK : K.RobustlyHurwitz) (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (i j k : Fin n) (hij : i < j) (hjk : j < k)
    (hijc : phaseCorner (q i) = phaseCorner (q j))
    (hikc : phaseCorner (q i) = phaseCorner (q k)) : False := by
  apply stable_pairing_no_three_contacts (hK _ (K.corner_mem _)) hb
    (hw _ (K.corner_mem _)) (T.positive i) (T.increasing hij) (T.increasing hjk)
    (T.contacts i)
  · rw [hijc]; exact T.contacts j
  · rw [hikc]; exact T.contacts k

theorem no_ab (T : PhaseContacts K b q) (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : q i = 1) (hj : q j = 1) (hk : q k = 2) (hl : q l = 2) : False := by
  apply K.stable_no_ordered_ab_contacts hK hb hb0 hw
    (T.positive i) (T.increasing hij) (T.increasing hjk) (T.increasing hkl)
  · simpa [hi,phaseCorner] using T.contacts i
  · simpa [hj,phaseCorner] using T.contacts j
  · simpa [hk,phaseCorner] using T.contacts k
  · simpa [hl,phaseCorner] using T.contacts l

theorem no_quartic_origin_double (T : PhaseContacts K b q) (hK : K.RobustlyHurwitz)
    (hb : b ≠ 0) (hb0 : b 0 = 0) (hb5 : b 5 = 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (i j : Fin n) (hij : i < j) (hijc : phaseCorner (q i) = phaseCorner (q j)) : False := by
  apply stable_no_origin_two_quartic_contacts (hK _ (K.corner_mem _)) hb hb0 hb5
    (hw _ (K.corner_mem _)) (T.positive i) (T.increasing hij) (T.contacts i)
  rw [hijc]
  exact T.contacts j

theorem no_origin_bc (T : PhaseContacts K b q) (hK : K.RobustlyHurwitz)
    (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : b 5 = 0) (hwidth : K.FullWidth)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : q i = 2) (hj : q j = 2) (hk : q k = 3) (hl : q l = 3) : False := by
  apply K.stable_no_origin_ordered_bc_contacts hK hb0 hb1 hb5 hwidth.2.2.1 hw
    (T.positive i) (T.increasing hij) (T.increasing hjk) (T.increasing hkl)
  · simpa [hi,phaseCorner] using T.contacts i
  · simpa [hj,phaseCorner] using T.contacts j
  · simpa [hk,phaseCorner] using T.contacts k
  · simpa [hl,phaseCorner] using T.contacts l

end PhaseContacts

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

def phaseContacts (C : DistinctMomentCertificate K b) {hi : ℕ} (P : CertificatePhases C hi)
    (hhi : hi ≤ 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {n : ℕ} (hn : C.nodes.card = n) (hp : ∀ r ∈ C.nodes, 0 < r) :
    PhaseContacts K b (fun i => P.phase (C.nodes.orderEmbOfFin hn i)) where
  t := C.nodes.orderEmbOfFin hn
  positive := fun i => hp _ (C.nodes.orderEmbOfFin_mem hn i)
  increasing := (C.nodes.orderEmbOfFin hn).strictMono
  contacts := fun i => (K.phase_corner_contact (C.contains _ (C.nodes.orderEmbOfFin_mem hn i))
    (hp _ (C.nodes.orderEmbOfFin_mem hn i)) hw (C.contacts _ (C.nodes.orderEmbOfFin_mem hn i))
    ((P.upper _).trans_le hhi) (P.signs _ (C.nodes.orderEmbOfFin_mem hn i)
      (hp _ (C.nodes.orderEmbOfFin_mem hn i)))).1

def phaseContacts_tail (C : DistinctMomentCertificate K b) {hi : ℕ} (P : CertificatePhases C hi)
    (hhi : hi ≤ 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {m : ℕ} (hn : C.nodes.card = m+1) :
    PhaseContacts K b (fun i : Fin m => P.phase (C.nodes.orderEmbOfFin hn i.succ)) := by
  have hp (i : Fin m) : 0 < C.nodes.orderEmbOfFin hn i.succ :=
    (C.nonneg _ (C.nodes.orderEmbOfFin_mem hn 0)).trans_lt
      ((C.nodes.orderEmbOfFin hn).strictMono (Fin.succ_pos i))
  exact {
    t := fun i => C.nodes.orderEmbOfFin hn i.succ
    positive := hp
    increasing := (C.nodes.orderEmbOfFin hn).strictMono.comp (fun i j hij => Fin.succ_lt_succ_iff.mpr hij)
    contacts := fun i => (K.phase_corner_contact (C.contains _ (C.nodes.orderEmbOfFin_mem hn i.succ))
      (hp i) hw (C.contacts _ (C.nodes.orderEmbOfFin_mem hn i.succ)) ((P.upper _).trans_le hhi)
      (P.signs _ (C.nodes.orderEmbOfFin_mem hn i.succ) (hp i))).1 }

end DistinctMomentCertificate
end
end SPR.N5.Direct
