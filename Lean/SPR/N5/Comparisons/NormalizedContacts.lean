import SPR.N5.Contacts.PhaseContacts
import SPR.N5.Comparisons.Contacts

/-!
# NormalizedContacts

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
归一化实际接触多项式，证明线性余因子常数为正并给出公共分量取值。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial

/-- Normalize a quintic double-contact factorization by its positive leading
coefficient. The remainder constant is strictly positive because b5*a5>0. -/
theorem stable_normalized_doubleContact {a : Poly5} (ha : IsHurwitz a.toPoly)
    {b : Vec6} (hb0 : 0 < b 0) (hb5 : 0 < b 5)
    (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hpr : generalPairing a b r = 0) (hps : generalPairing a b s = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ t, generalPairing a b t = b 0 * doubleContact r s d t := by
  have hb : b ≠ 0 := by intro he; simp [he] at hb0
  obtain ⟨d,hd,hform⟩ := stable_two_contacts_factorization ha hb hw hr hrs hpr hps
  have hconst := pairingPoly_constant a b
  rw [hform,contactPoly_coeff_zero] at hconst
  have hdpos : 0 < d := by
    have hp : 0 < d * (r*s)^2 := hconst ▸ mul_pos hb5 (quintic_constant_pos ha)
    exact (mul_pos_iff_of_pos_right (sq_pos_of_pos (mul_pos hr (hr.trans hrs)))).mp hp
  refine ⟨d / b 0,div_pos hdpos hb0,?_⟩
  intro t
  rw [← pairingPoly_eval,hform]
  simp only [contactPoly,eval_mul,eval_add,eval_sub,eval_pow,eval_C,eval_X,doubleContact]
  field_simp [ne_of_gt hb0]

namespace Box5

theorem pairing_at_even_root_odd_upper (K : Box5) {b : Vec6}
    (D : QuinticNumeratorInterlacing b) (R : RootBands K)
    {t : ℝ} (ht : t = D.e ∨ t = D.f) (c : Corner) (hc : c = .B ∨ c = .C) :
    generalPairing (K.corner c) b t = b 0 * oddProduct D.k D.l R.oU R.pL t := by
  have hE : numeratorEven b t = 0 := by
    rw [(D.component_values t).1]
    rcases ht with rfl | rfl <;> simp
  have hO : oddPart (K.corner c) t = K.oddUpper t := by rcases hc with rfl | rfl <;> rfl
  rw [generalPairing,hE,zero_mul,zero_add,hO,R.odd_upper,(D.component_values t).2]
  unfold oddProduct
  ring

theorem pairing_at_even_root_odd_lower (K : Box5) {b : Vec6}
    (D : QuinticNumeratorInterlacing b) (R : RootBands K)
    {t : ℝ} (ht : t = D.e ∨ t = D.f) (c : Corner) (hc : c = .A ∨ c = .D) :
    generalPairing (K.corner c) b t = b 0 * oddProduct D.k D.l R.oL R.pU t := by
  have hE : numeratorEven b t = 0 := by
    rw [(D.component_values t).1]
    rcases ht with rfl | rfl <;> simp
  have hO : oddPart (K.corner c) t = K.oddLower t := by rcases hc with rfl | rfl <;> rfl
  rw [generalPairing,hE,zero_mul,zero_add,hO,R.odd_lower,(D.component_values t).2]
  unfold oddProduct
  ring

theorem pairing_at_odd_root_even_lower (K : Box5) {b : Vec6}
    (D : QuinticNumeratorInterlacing b) (R : RootBands K)
    {t : ℝ} (ht : t = D.k ∨ t = D.l) (c : Corner) (hc : c = .C ∨ c = .D) :
    generalPairing (K.corner c) b t = (b 1*K.lower.a1) * evenProduct D.e D.f R.eL R.fU t := by
  have hO : numeratorOdd b t = 0 := by
    rw [(D.component_values t).2]
    rcases ht with rfl | rfl <;> simp
  have hE : evenPart (K.corner c) t = K.evenLower t := by rcases hc with rfl | rfl <;> rfl
  rw [generalPairing,hO,zero_mul,mul_zero,add_zero,hE,R.even_lower,(D.component_values t).1]
  unfold evenProduct
  ring

end Box5
end
end SPR.N5.Direct
