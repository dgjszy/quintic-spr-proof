import SPR.N5.Comparisons.FinalFiveExclusion
import SPR.N5.Comparisons.TerminalCertificate
import SPR.N5.Critical.FullWidthCritical

/-!
# Exclusion of the critical finite representation

This is the assembly used in paper §7. The algebra and interpolation of §4 give
exactly two support shapes. Section 5 excludes the quartic and zero-node cases;
the remaining positive quintic case reduces to Q1–Q5 and uses the ratios of §6.
The critical numerator is only nonnegative and may have degree four. It is not
the strictly positive numerator asserted by the final theorem in `Main`.
-/

namespace SPR.N5.Direct
noncomputable section

namespace DistinctMomentCertificate
variable {K : Box5} {b : Vec6}

/-- Six positive finite nodes with a quintic numerator reduce to Q1–Q5, all of
which contradict the common-component ratio comparisons of paper §6. -/
theorem no_positive_quintic_six_nodes (C : DistinctMomentCertificate K b)
    (hK : K.RobustlyHurwitz) (hwidth : K.FullWidth) (R : RootBands K)
    (D : QuinticNumeratorInterlacing b) (P : CertificatePhases C 5)
    (hP : P.phase = D.phase) (hb : b ≠ 0)
    (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : 0 ≤ b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hn : C.nodes.card = 6) (hp : ∀ r ∈ C.nodes, 0 < r)
    {c : ℝ} (hc : c ≠ 0)
    (hU : C.U = Polynomial.C c * numeratorOddPoly b)
    (hV : C.V = -(Polynomial.C c * numeratorEvenPoly b)) : False := by
  let q : Fin 6 → ℕ := fun i => P.phase (C.nodes.orderEmbOfFin hn i)
  let T : PhaseContacts K b q := C.phaseContacts P (by decide) hw hn hp
  -- Appendix A provides necessary candidates; contact multiplicities leave five rows.
  have hcandidate := C.candidate_no_origin_enumerated hK R P (by decide) hn
    (Or.inr rfl) hp hc hU hV
  obtain ⟨hneg, hrow⟩ := T.quintic_candidate_reduction hK hb hb0.le hw hcandidate
  rw [hneg] at hrow
  -- A missing zero node does not yet imply b₅ > 0. Exclude b₅ = 0 separately.
  have hb5pos : 0 < b 5 := T.finalFive_constant_pos hK hwidth hb0 hb1 hb5 hw
    (fun hzero i => P.origin_lower hzero _
      (C.nonneg _ (C.nodes.orderEmbOfFin_mem hn i))) hrow
  let S : TerminalContacts K b D q := C.terminalContacts D P hP hw hn hp hc hneg hU hV
  exact S.finalFive_impossible hK hwidth hb0 hb1 hb5pos hw R hrow

end DistinctMomentCertificate

/-- No nondegenerate stable coefficient box carries the nonzero nonnegative
numerator and finite moment representation forced by synthesis failure. -/
theorem Box5.no_weak_moment_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (M : MomentCertificate K b) : False := by
  -- §3: merge equal frequencies without changing the moment or contact equations.
  let C := M.merge
  -- §4: coefficient signs, coprimality and the constant interpolation multiplier.
  obtain ⟨hb1, hb2, _, hb4, hb5⟩ :=
    K.weak_numerator_coefficients hK hwidth hb hb0 hw
  have hcoprime := K.weak_numerator_isCoprime hK hwidth hb hb0 hw
  have hUne := C.U_ne_zero hK hwidth hb hw
  obtain ⟨c, hc, hU, hV⟩ := C.constant_multiplier hUne (ne_of_gt hb1) hcoprime
  obtain ⟨R⟩ := K.rootBands hK hwidth
  rcases C.support_dichotomy hUne (ne_of_gt hb1) hcoprime with hfive | hsix
  · -- Five finite nodes and positive infinity mass: the numerator is quartic.
    obtain ⟨hn, hinfinity, hbzero⟩ := hfive
    obtain ⟨D⟩ := K.weak_quartic_interlacing hK hwidth hb hbzero hw
    obtain ⟨P, _⟩ := C.quartic_phases D hK hwidth hb hb1 hb2 hw
    have hcpos := C.multiplier_positive_at_infinity hb1 hn hinfinity hV
    exact C.no_five_nodes hK R P hb hbzero hb4 hw hn hcpos hU hV
  · -- Six finite nodes: retain both numerator degrees and the zero-node boundary.
    obtain ⟨hn, _⟩ := hsix
    rcases eq_or_lt_of_le hb0 with hbzero | hbpos
    · obtain ⟨D⟩ := K.weak_quartic_interlacing hK hwidth hb hbzero.symm hw
      obtain ⟨P, _⟩ := C.quartic_phases D hK hwidth hb hb1 hb2 hw
      exact C.no_quartic_six_nodes hK R P hb hbzero.symm hb4 hw hn hc hU hV
    · obtain ⟨D⟩ := K.weak_quintic_interlacing hK hwidth hb hbpos hw
      obtain ⟨P, hP⟩ := C.quintic_phases D hK hwidth hb hbpos hb1 hw
      by_cases hzero : 0 ∈ C.nodes
      · exact C.no_quintic_origin hK R P hwidth hbpos hb1 hb4 hw hn hc hU hV hzero
      · exact C.no_positive_quintic_six_nodes hK hwidth R D P hP hb hbpos hb1 hb5 hw
          hn (C.positive_nodes_of_no_zero hzero) hc hU hV

end
end SPR.N5.Direct
