import SPR.N5.Contacts.ContactSigns

/-!
# CornerContacts

论文 §5：接触点重数、符号和极小顶点之间的联系。
证明正接触可转移到相应极小顶点，且分母两分量的取值保持。
-/

namespace SPR.N5.Direct
noncomputable section

def phaseCorner : ℕ → Corner
  | 1 => .A
  | 2 => .B
  | 3 => .C
  | _ => .D

theorem contact_terms_equal {x y u v : ℝ}
    (hxy : 0 ≤ x+y) (huv : u+v = 0) (hx : x ≤ u) (hy : y ≤ v) :
    x = u ∧ y = v ∧ x+y = 0 := by
  constructor
  · linarith
  · constructor <;> linarith

theorem Box5.contact_at_component_minimum (K : Box5) {a : Poly5} {b : Vec6}
    {r : ℝ} (hr : 0 < r) (hE : numeratorEven b r ≠ 0) (hO : numeratorOdd b r ≠ 0)
    (ha : generalPairing a b r = 0) (c : Corner)
    (hw : 0 ≤ generalPairing (K.corner c) b r)
    (he : numeratorEven b r * evenPart (K.corner c) r ≤ numeratorEven b r * evenPart a r)
    (ho : r * (numeratorOdd b r * oddPart (K.corner c) r) ≤ r * (numeratorOdd b r * oddPart a r)) :
    generalPairing (K.corner c) b r = 0 ∧
      evenPart (K.corner c) r = evenPart a r ∧ oddPart (K.corner c) r = oddPart a r := by
  obtain ⟨h1,h2,h3⟩ := contact_terms_equal hw ha he ho
  refine ⟨h3,mul_left_cancel₀ hE h1,?_⟩
  exact mul_left_cancel₀ hO (mul_left_cancel₀ (ne_of_gt hr) h2)

/-- Each positive contact also contacts its sign-selected corner, with the same
actual denominator components. No unproved uniqueness of coefficients is used. -/
theorem Box5.phase_corner_contact (K : Box5) {a : Poly5} {b : Vec6} {r : ℝ}
    (ha : K.Contains a) (hr : 0 < r)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hc : generalPairing a b r = 0) {s : ℕ} (hs : s < 5)
    (hsgn : StageSigns s (numeratorEven b r) (numeratorOdd b r)) :
    generalPairing (K.corner (phaseCorner s)) b r = 0 ∧
      evenPart (K.corner (phaseCorner s)) r = evenPart a r ∧
      oddPart (K.corner (phaseCorner s)) r = oddPart a r := by
  obtain ⟨hel,heu,hol,hou⟩ := K.component_bounds ha hr.le
  have hE : numeratorEven b r ≠ 0 := by
    interval_cases s <;> first | exact ne_of_lt hsgn.1 | exact ne_of_gt hsgn.1
  have hO : numeratorOdd b r ≠ 0 := by
    interval_cases s <;> first | exact ne_of_lt hsgn.2 | exact ne_of_gt hsgn.2
  apply K.contact_at_component_minimum hr hE hO hc (phaseCorner s)
    (hw _ (K.corner_mem _) r hr.le)
  · interval_cases s
    · exact mul_le_mul_of_nonneg_left hel hsgn.1.le
    · exact mul_le_mul_of_nonpos_left heu hsgn.1.le
    · exact mul_le_mul_of_nonpos_left heu hsgn.1.le
    · exact mul_le_mul_of_nonneg_left hel hsgn.1.le
    · exact mul_le_mul_of_nonneg_left hel hsgn.1.le
  · apply mul_le_mul_of_nonneg_left _ hr.le
    interval_cases s
    · exact mul_le_mul_of_nonneg_left hol hsgn.2.le
    · exact mul_le_mul_of_nonneg_left hol hsgn.2.le
    · exact mul_le_mul_of_nonpos_left hou hsgn.2.le
    · exact mul_le_mul_of_nonpos_left hou hsgn.2.le
    · exact mul_le_mul_of_nonneg_left hol hsgn.2.le

end
end SPR.N5.Direct
