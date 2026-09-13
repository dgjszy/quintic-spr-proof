import SPR.N5.Comparisons.NormalizedContacts

/-!
# PhaseBounds

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
把最终六节点的区间编号和符号转换为根界；定义 TerminalContacts。
-/

namespace SPR.N5.Direct
noncomputable section

namespace QuinticNumeratorInterlacing
variable {b : Vec6}

def Bounds (D : QuinticNumeratorInterlacing b) (s : ℕ) (t : ℝ) : Prop :=
  match s with
  | 0 => t < D.e
  | 1 => D.e < t ∧ t < D.k
  | 2 => D.k < t ∧ t < D.f
  | 3 => D.f < t ∧ t < D.l
  | 4 => D.l < t
  | _ => False

theorem bounds_of_phase (D : QuinticNumeratorInterlacing b) {t : ℝ} {s : ℕ}
    (hE : numeratorEven b t ≠ 0) (hO : numeratorOdd b t ≠ 0) (hs : D.phase t = s) :
    D.Bounds s t := by
  obtain ⟨hEv,hOv⟩ := D.component_values t
  have hte : t ≠ D.e := by intro he; rw [hEv,he] at hE; simp at hE
  have htf : t ≠ D.f := by intro he; rw [hEv,he] at hE; simp at hE
  have htk : t ≠ D.k := by intro he; rw [hOv,he] at hO; simp at hO
  have htl : t ≠ D.l := by intro he; rw [hOv,he] at hO; simp at hO
  unfold phase at hs
  split_ifs at hs with he hk hf hl
  · subst s; exact he
  · subst s; exact ⟨lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hte),hk⟩
  · subst s; exact ⟨lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm htk),hf⟩
  · subst s; exact ⟨lt_of_le_of_ne (le_of_not_gt hf) (Ne.symm htf),hl⟩
  · subst s; exact lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm htl)

end QuinticNumeratorInterlacing

/-- Geometric and sign information retained for the five terminal words. -/
structure TerminalContacts (K : Box5) (b : Vec6) (D : QuinticNumeratorInterlacing b)
    (q : Fin 6 → ℕ) extends PhaseContacts K b q where
  phases : ∀ i, D.phase (t i) = q i
  denominator_signs : ∀ i,
    StageSigns (Classification.codeAt 6 false q i)
      (evenPart (K.corner (phaseCorner (q i))) (t i))
      (oddPart (K.corner (phaseCorner (q i))) (t i))

namespace TerminalContacts
variable {K : Box5} {b : Vec6} {D : QuinticNumeratorInterlacing b} {q : Fin 6 → ℕ}

theorem bounds (T : TerminalContacts K b D q) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (i : Fin 6) : D.Bounds (q i) (T.t i) :=
  D.bounds_of_phase
    (K.positive_contact_even_ne_zero hK hwidth hb hw (K.corner_mem _) (T.positive i) (T.contacts i))
    (K.positive_contact_odd_ne_zero hK hwidth hb hw (K.corner_mem _) (T.positive i) (T.contacts i))
    (T.phases i)

end TerminalContacts
end
end SPR.N5.Direct
