import SPR.N5.Classification.WordPaths
import SPR.N5.Contacts.CornerContacts

/-!
# PhaseCertificate

论文 §5：接触点重数、符号和极小顶点之间的联系。
从分子交错结构提取分类所需的区间编号、单调性和节点符号。
-/

namespace SPR.N5.Direct
noncomputable section

/-- Only the phase information needed to feed the finite classification. -/
structure CertificatePhases {K : Box5} {b : Vec6} (C : DistinctMomentCertificate K b) (hi : ℕ) where
  phase : ℝ → ℕ
  monotone : Monotone phase
  upper : ∀ t, phase t < hi
  signs : ∀ t ∈ C.nodes, 0 < t → StageSigns (phase t) (numeratorEven b t) (numeratorOdd b t)
  origin_lower : b 5 = 0 → ∀ t, 0 ≤ t → 1 ≤ phase t

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem quintic_phases (C : DistinctMomentCertificate K b) (D : QuinticNumeratorInterlacing b)
    (hK : K.RobustlyHurwitz) (hwidth : K.FullWidth) (hb : b ≠ 0)
    (hb0 : 0 < b 0) (hb1 : 0 < b 1)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    ∃ P : CertificatePhases C 5, P.phase = D.phase := by
  refine ⟨⟨D.phase,D.phase_monotone,D.phase_lt,?_,?_⟩,rfl⟩
  · intro r hr hp
    exact D.phase_signs hb0 hb1
      (K.positive_contact_even_ne_zero hK hwidth hb hw (C.contains r hr) hp (C.contacts r hr))
      (K.positive_contact_odd_ne_zero hK hwidth hb hw (C.contains r hr) hp (C.contacts r hr))
  · intro hz t ht
    exact D.phase_pos_of_origin ((D.origin_iff hb1).mp hz) ht

theorem quartic_phases (C : DistinctMomentCertificate K b) (D : QuarticNumeratorInterlacing b)
    (hK : K.RobustlyHurwitz) (hwidth : K.FullWidth) (hb : b ≠ 0)
    (hb1 : 0 < b 1) (hb2 : 0 < b 2)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    ∃ P : CertificatePhases C 4, P.phase = D.phase := by
  refine ⟨⟨D.phase,D.phase_monotone,D.phase_lt,?_,?_⟩,rfl⟩
  · intro r hr hp
    exact D.phase_signs hb1 hb2
      (K.positive_contact_even_ne_zero hK hwidth hb hw (C.contains r hr) hp (C.contacts r hr))
      (K.positive_contact_odd_ne_zero hK hwidth hb hw (C.contains r hr) hp (C.contacts r hr))
  · intro hz t ht
    exact D.phase_pos_of_origin ((D.origin_iff hb1).mp hz) ht

end DistinctMomentCertificate

namespace Classification

def codeAt (n : ℕ) (neg : Bool) (q : Fin n → ℕ) (i : Fin n) : ℕ :=
  if ((n-1-i.val)%2 == 1) != neg then (rotated (q i)+2)%4 else rotated (q i)

theorem rotated_lt {s : ℕ} (hs : s < 5) : rotated s < 4 := by
  interval_cases s <;> norm_num [rotated]

theorem codeAt_lt {n : ℕ} (neg : Bool) {q : Fin n → ℕ} (hq : ∀ i, q i < 5) (i : Fin n) :
    codeAt n neg q i < 4 := by
  unfold codeAt
  split_ifs
  · exact Nat.mod_lt _ (by decide)
  · exact rotated_lt (hq i)

end Classification

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

theorem ordered_contact_signs (C : DistinctMomentCertificate K b) {hi : ℕ}
    (P : CertificatePhases C hi) (hhi : hi ≤ 5) {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b))
    (i : Fin C.nodes.card) (hp : 0 < C.orderedNode i) :
    StageSigns (Classification.codeAt C.nodes.card (decide (c < 0))
      (fun j => P.phase (C.orderedNode j)) i)
      (evenPart (C.a (C.orderedNode i)) (C.orderedNode i))
      (oddPart (C.a (C.orderedNode i)) (C.orderedNode i)) := by
  have hr := C.orderedNode_mem i
  obtain ⟨hA,hB⟩ := C.node_multiplier_identities hU hV hr
  have hs := contact_stageSigns ((P.upper _).trans_le hhi) (P.signs _ hr hp)
    (C.positive _ hr) hp hA hB
  have hsgn := signed_weight_product (C.orderedNode_weight_sign i) hc
  unfold Classification.codeAt
  split_ifs with hf
  · apply hs.2
    simpa only [hf,if_true] using hsgn
  · apply hs.1
    simpa only [hf,if_false] using hsgn

theorem zero_contact_constant (C : DistinctMomentCertificate K b) (hK : K.RobustlyHurwitz)
    (hz : 0 ∈ C.nodes) : b 5 = 0 :=
  (origin_contact_iff_constant_zero (hK _ (C.contains 0 hz)) b).mp (C.contacts 0 hz)

theorem zero_contact_multiplier_positive (C : DistinctMomentCertificate K b)
    (hK : K.RobustlyHurwitz) (hb4 : 0 < b 4) {c : ℝ}
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) (hz : 0 ∈ C.nodes) :
    0 < c * Lagrange.nodalWeight C.nodes id 0 := by
  have he := (C.node_multiplier_identities hU hV hz).1
  have ha5 := quintic_constant_pos (hK _ (C.contains 0 hz))
  have hp : 0 < C.z 0 := by simpa [z,evenPart] using mul_pos (C.positive 0 hz) ha5
  rw [he] at hp
  simpa only [numeratorOdd,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_self,zero_add] using
    (mul_pos_iff_of_pos_right (show 0 < numeratorOdd b 0 by simpa [numeratorOdd] using hb4)).mp hp

end DistinctMomentCertificate
end
end SPR.N5.Direct
