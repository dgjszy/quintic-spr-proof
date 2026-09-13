import SPR.N5.Contacts.PairingNonzero

/-! Local contact obstructions now consume actual Hurwitz denominators and
nonzero weak numerators, without an extra nonzero-pairing assumption.
## 与论文的对应

论文 §5：接触点重数、符号和极小顶点之间的联系。
将局部重数和系数矛盾应用于真实稳定分母，不额外假设配对多项式非零。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial

theorem stable_pairing_no_three_contacts {a : Poly5} (ha : IsHurwitz a.toPoly)
    {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s u : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u)
    (hpr : generalPairing a b r = 0) (hps : generalPairing a b s = 0)
    (hpu : generalPairing a b u = 0) : False :=
  pairingPoly_no_three_contacts a b (pairingPoly_ne_zero_of_hurwitz a ha b hb)
    hw hr hrs hsu hpr hps hpu

theorem stable_two_contacts_factorization {a : Poly5} (ha : IsHurwitz a.toPoly)
    {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hpr : generalPairing a b r = 0) (hps : generalPairing a b s = 0) :
    ∃ d : ℝ, 0 ≤ d ∧ pairingPoly a b = contactPoly (b 0) d r s := by
  simpa only [pairingPoly_coeff_five] using
    two_contacts_factorization (pairingPoly_ne_zero_of_hurwitz a ha b hb)
      (pairingPoly_degree_le a b) (by simpa only [pairingPoly_eval] using hw)
      hr hrs (by simpa only [pairingPoly_eval] using hpr)
      (by simpa only [pairingPoly_eval] using hps)

theorem stable_no_origin_two_quartic_contacts {a : Poly5} (ha : IsHurwitz a.toPoly)
    {b : Vec6} (hb : b ≠ 0) (hb0 : b 0 = 0) (hb5 : b 5 = 0)
    (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hpr : generalPairing a b r = 0) (hps : generalPairing a b s = 0) : False := by
  apply no_origin_and_two_quartic_contacts (pairingPoly_ne_zero_of_hurwitz a ha b hb)
    (pairingPoly_quartic_degree_le a b hb0)
    (by simpa only [pairingPoly_eval] using hw) ?_ hr hrs
    (by simpa only [pairingPoly_eval] using hpr)
    (by simpa only [pairingPoly_eval] using hps)
  rw [pairingPoly_eval]
  exact (origin_contact_iff_constant_zero ha b).mpr hb5

theorem Box5.stable_no_ordered_ab_contacts (K : Box5) (hK : K.RobustlyHurwitz)
    {b : Vec6} (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s u v : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (har : generalPairing (K.corner .A) b r = 0)
    (has : generalPairing (K.corner .A) b s = 0)
    (hbu : generalPairing (K.corner .B) b u = 0)
    (hbv : generalPairing (K.corner .B) b v = 0) : False :=
  K.no_ordered_ab_contacts b hb0
    (pairingPoly_ne_zero_of_hurwitz _ (hK _ (K.corner_mem .A)) b hb)
    (pairingPoly_ne_zero_of_hurwitz _ (hK _ (K.corner_mem .B)) b hb)
    (hw _ (K.corner_mem .A)) (hw _ (K.corner_mem .B)) hr hrs hsu huv har has hbu hbv

theorem Box5.stable_no_origin_ordered_bc_contacts (K : Box5) (hK : K.RobustlyHurwitz)
    {b : Vec6} (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : b 5 = 0)
    (hwidth : K.lower.a3 < K.upper.a3)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s u v : ℝ} (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hbr : generalPairing (K.corner .B) b r = 0)
    (hbs : generalPairing (K.corner .B) b s = 0)
    (hcu : generalPairing (K.corner .C) b u = 0)
    (hcv : generalPairing (K.corner .C) b v = 0) : False := by
  have hb : b ≠ 0 := by intro he; simp [he] at hb0
  exact K.no_origin_ordered_bc_contacts b hb0 hb1 hb5 hwidth
    (pairingPoly_ne_zero_of_hurwitz _ (hK _ (K.corner_mem .B)) b hb)
    (pairingPoly_ne_zero_of_hurwitz _ (hK _ (K.corner_mem .C)) b hb)
    (hw _ (K.corner_mem .B)) (hw _ (K.corner_mem .C)) hr hrs hsu huv hbr hbs hcu hcv

theorem MomentCertificate.constant_zero_of_origin_atom {K : Box5} {b : Vec6}
    (M : MomentCertificate K b) (hK : K.RobustlyHurwitz)
    (i : Fin M.n) (hi : 0 < M.μ i) (ht : M.t i = 0) : b 5 = 0 := by
  have hc := M.contacts i hi
  rw [ht] at hc
  exact (origin_contact_iff_constant_zero (hK _ (M.contains i)) b).mp hc

theorem MomentCertificate.positive_frequency_of_constant_pos {K : Box5} {b : Vec6}
    (M : MomentCertificate K b) (hK : K.RobustlyHurwitz) (hb5 : 0 < b 5)
    (i : Fin M.n) (hi : 0 < M.μ i) : 0 < M.t i := by
  apply lt_of_le_of_ne (M.frequency_nonneg i)
  intro he
  exact (ne_of_gt hb5) (M.constant_zero_of_origin_atom hK i hi he.symm)

/-- The original infeasibility assumption now supplies nonzero pairing polynomials
for every denominator in the stable critical box, as well as b₅ ≥ 0. -/
theorem Box5.critical_stable_moment_certificate (K : Box5) (hK : K.RobustlyHurwitz)
    (hno : ¬ ∃ b : ℝ[X], b.natDegree = 5 ∧
      ∀ a : Poly5, K.Contains a → FrequencySPR a.toPoly b) :
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ 1 ∧ (K.contract θ hθ.le).RobustlyHurwitz ∧
      ∃ b : Vec6, ‖b‖ = 1 ∧ numeratorPoly b ≠ 0 ∧ 0 ≤ b 0 ∧ 0 ≤ b 5 ∧
        (∀ a : Poly5, (K.contract θ hθ.le).Contains a →
          pairingPoly a b ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) ∧
        Nonempty (MomentCertificate (K.contract θ hθ.le) b) := by
  obtain ⟨θ, hθ, hθ1, hstable, b, hnorm, hpoly, hb0, hweak, hM⟩ :=
    K.critical_moment_certificate hK hno
  have hb : b ≠ 0 := by intro he; simp [he] at hnorm
  have hb5 := weak_numerator_constant_nonneg
    (hstable _ (K.contract θ hθ.le).lower_mem)
    (hweak _ (K.contract θ hθ.le).lower_mem)
  exact ⟨θ, hθ, hθ1, hstable, b, hnorm, hpoly, hb0, hb5,
    (fun a ha => ⟨pairingPoly_ne_zero_of_hurwitz a (hstable a ha) b hb, hweak a ha⟩), hM⟩

end
end SPR.N5.Direct
