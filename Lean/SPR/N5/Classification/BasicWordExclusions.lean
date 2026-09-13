import SPR.N5.Contacts.PhaseContacts

/-!
# BasicWordExclusions

论文 §5 与附录 A：必要候选表的完备性及基本排除。
把表中具体序列归约到三接触、A/B 次序或零常数项 B/C 排除引理。
-/

namespace SPR.N5.Direct
noncomputable section

namespace PhaseContacts
variable {K : Box5} {b : Vec6}

theorem exclude_11223 {q : Fin 5 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hq : List.ofFn q = [1,1,2,2,3]) : False := by
  have he : q = ![1,1,2,2,3] := List.ofFn_injective
    (hq.trans (by decide : List.ofFn ![1,1,2,2,3] = [1,1,2,2,3]).symm)
  apply T.no_ab hK hb hb0 hw 0 1 2 3 (by decide) (by decide) (by decide)
    <;> rw [he] <;> rfl

theorem exclude_011223 {q : Fin 6 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hq : List.ofFn q = [0,1,1,2,2,3]) : False := by
  have he : q = ![0,1,1,2,2,3] := List.ofFn_injective
    (hq.trans (by decide : List.ofFn ![0,1,1,2,2,3] = [0,1,1,2,2,3]).symm)
  apply T.no_ab hK hb hb0 hw 1 2 3 4 (by decide) (by decide) (by decide)
    <;> rw [he] <;> rfl

theorem exclude_112233 {q : Fin 6 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hq : List.ofFn q = [1,1,2,2,3,3]) : False := by
  have he : q = ![1,1,2,2,3,3] := List.ofFn_injective
    (hq.trans (by decide : List.ofFn ![1,1,2,2,3,3] = [1,1,2,2,3,3]).symm)
  apply T.no_ab hK hb hb0 hw 0 1 2 3 (by decide) (by decide) (by decide)
    <;> rw [he] <;> rfl

theorem exclude_quartic_origin_1223 {q : Fin 4 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : b 0 = 0) (hb5 : b 5 = 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hq : List.ofFn q = [1,2,2,3]) : False := by
  have he : q = ![1,2,2,3] := List.ofFn_injective
    (hq.trans (by decide : List.ofFn ![1,2,2,3] = [1,2,2,3]).symm)
  apply T.no_quartic_origin_double hK hb hb0 hb5 hw 1 2 (by decide)
  rw [he]
  rfl

theorem exclude_quartic_origin_12233 {q : Fin 5 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb : b ≠ 0) (hb0 : b 0 = 0) (hb5 : b 5 = 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hq : List.ofFn q = [1,2,2,3,3]) : False := by
  have he : q = ![1,2,2,3,3] := List.ofFn_injective
    (hq.trans (by decide : List.ofFn ![1,2,2,3,3] = [1,2,2,3,3]).symm)
  apply T.no_quartic_origin_double hK hb hb0 hb5 hw 1 2 (by decide)
  rw [he]
  rfl

theorem exclude_quintic_origin_12233 {q : Fin 5 → ℕ} (T : PhaseContacts K b q)
    (hK : K.RobustlyHurwitz) (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : b 5 = 0)
    (hwidth : K.FullWidth)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hq : List.ofFn q = [1,2,2,3,3]) : False := by
  have he : q = ![1,2,2,3,3] := List.ofFn_injective
    (hq.trans (by decide : List.ofFn ![1,2,2,3,3] = [1,2,2,3,3]).symm)
  apply T.no_origin_bc hK hb0 hb1 hb5 hwidth hw 1 2 3 4 (by decide) (by decide) (by decide)
    <;> rw [he] <;> rfl

end PhaseContacts
end
end SPR.N5.Direct
