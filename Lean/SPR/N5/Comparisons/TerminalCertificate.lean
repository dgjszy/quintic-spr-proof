import SPR.N5.Comparisons.PhaseBounds

/-!
# From the finite representation to the five contact configurations

Paper §5, equation (5.4) and the paragraph following Table 2. The interval index
comes from the numerator roots; the denominator signs also depend on the node.
`DistinctMomentCertificate.terminalContacts` transfers both pieces of information
to the same corner contacts. It makes no assertion that a candidate row is realizable.
-/

namespace SPR.N5.Direct
noncomputable section

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

/-- Transfer the ordered nodes, numerator intervals and interpolated denominator
signs to the corner configuration used in the three ratio comparisons. -/
def terminalContacts (C : DistinctMomentCertificate K b)
    (D : QuinticNumeratorInterlacing b) (P : CertificatePhases C 5)
    (hP : P.phase = D.phase)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hn : C.nodes.card = 6) (hp : ∀ r ∈ C.nodes, 0 < r)
    {c : ℝ} (hc : c ≠ 0) (hneg : decide (c < 0) = false)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) :
    TerminalContacts K b D (fun i => P.phase (C.nodes.orderEmbOfFin hn i)) where
  toPhaseContacts := C.phaseContacts P (by decide) hw hn hp
  phases := fun i => by
    change D.phase (C.nodes.orderEmbOfFin hn i) = P.phase (C.nodes.orderEmbOfFin hn i)
    rw [hP]
  denominator_signs := fun i => by
    have hnode := C.nodes.orderEmbOfFin_mem hn i
    have hpositive := hp _ hnode
    have hsigns := C.contact_signs_enumerated hn P (by decide) hc hU hV i hpositive
    rw [hneg] at hsigns
    -- At a positive contact, both component values agree with the minimizing corner.
    have hcorner := K.phase_corner_contact (C.contains _ hnode) hpositive hw
      (C.contacts _ hnode) (P.upper _) (P.signs _ hnode hpositive)
    rw [← hcorner.2.1, ← hcorner.2.2] at hsigns
    exact hsigns

end DistinctMomentCertificate
end
end SPR.N5.Direct
