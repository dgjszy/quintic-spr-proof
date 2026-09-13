import SPR.N5.Classification.QuinticReduction
import SPR.N5.Comparisons.TerminalGeometry

/-!
# FinalFiveExclusion

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
先排除零常数项边界，再把五项候选分别归到三类比值矛盾。
-/

namespace SPR.N5.Direct
noncomputable section

namespace PhaseContacts
variable {K : Box5} {b : Vec6} {q : Fin 6 → ℕ}

/-- Paper §5: exclude b₅ = 0 even when zero is absent from the selected support. -/
theorem finalFive_constant_pos (T : PhaseContacts K b q) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : 0 ≤ b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (hlower : b 5 = 0 → ∀ i, 1 ≤ q i)
    (hrow : (false,false,List.ofFn q) ∈ Classification.finalFive) : 0 < b 5 := by
  by_contra hnotpos
  have hzero : b 5 = 0 := le_antisymm (le_of_not_gt hnotpos) hb5
  have hfirst : 1 ≤ q 0 := hlower hzero 0
  rcases Classification.finalFive_cases hrow with hQ1 | hQ2 | hQ3 | hQ4 | hQ5
  · -- Q1–Q4 start in I₀, which is empty when b₅ = 0.
    simp [hQ1] at hfirst
  · simp [hQ2] at hfirst
  · simp [hQ3] at hfirst
  · simp [hQ4] at hfirst
  · -- Q5 starts in I₁; the zero-constant-term B/C obstruction is needed instead.
    subst q
    exact T.no_origin_bc hK hb0 hb1 hzero hwidth hw 1 2 3 4
      (by decide) (by decide) (by decide) rfl rfl rfl rfl

end PhaseContacts

namespace TerminalContacts
variable {K : Box5} {b : Vec6} {D : QuinticNumeratorInterlacing b} {q : Fin 6 → ℕ}

/-- Paper §6: Q1/Q2 use A/D, Q3 uses C/D, and Q4/Q5 use B/C. -/
theorem finalFive_impossible (T : TerminalContacts K b D q) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : 0 < b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (R : RootBands K) (hrow : (false,false,List.ofFn q) ∈ Classification.finalFive) : False := by
  rcases Classification.finalFive_cases hrow with hQ1 | hQ2 | hQ3 | hQ4 | hQ5
  · -- Q1: the repeated A and D contacts use the common odd lower part (§6.2).
    subst q
    exact T.ad_impossible hK hwidth hb0 hb5 hw R rfl rfl rfl rfl
  · -- Q2 has the same A/D contact positions; its intermediate C contact is immaterial.
    subst q
    exact T.ad_impossible hK hwidth hb0 hb5 hw R rfl rfl rfl rfl
  · -- Q3: compare at the numerator odd-part roots using the common even part (§6.3).
    subst q
    exact T.cd_impossible hK hwidth hb0 hb1 hb5 hw R rfl rfl rfl rfl
  · -- Q4 and Q5 share the two B contacts followed by the two C contacts (§6.1).
    subst q
    exact T.bc_impossible hK hwidth hb0 hb1 hb5 hw R rfl rfl rfl rfl
  · subst q
    exact T.bc_impossible hK hwidth hb0 hb1 hb5 hw R rfl rfl rfl rfl

end TerminalContacts
end
end SPR.N5.Direct
