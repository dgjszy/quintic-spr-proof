import SPR.N5.Comparisons.PhaseBounds
import SPR.N5.Comparisons.TerminalContactBridges

/-!
# TerminalGeometry

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
由 Q1–Q5 的节点符号恢复三类严格根序，分别调用 B/C、A/D、C/D 矛盾。
-/

namespace SPR.N5.Direct
noncomputable section

theorem quadratic_pos_neg_crossing {a α β x y : ℝ} (ha : 0 < a) (hαβ : α < β)
    (hxy : x < y) (hp : 0 < a*((x-α)*(x-β))) (hn : a*((y-α)*(y-β)) < 0) :
    x < α ∧ α < y ∧ y < β := by
  have hneg := quadratic_negative_between ha hαβ hn
  have hpos := (quadratic_positive_iff ha hαβ).mp hp
  rcases hpos with hpos | hpos
  · exact ⟨hpos,hneg⟩
  · exfalso; linarith

theorem quadratic_neg_pos_crossing {a α β x y : ℝ} (ha : 0 < a) (hαβ : α < β)
    (hxy : x < y) (hn : a*((x-α)*(x-β)) < 0) (hp : 0 < a*((y-α)*(y-β))) :
    α < x ∧ x < β ∧ β < y := by
  have hneg := quadratic_negative_between ha hαβ hn
  have hpos := (quadratic_positive_iff ha hαβ).mp hp
  rcases hpos with hpos | hpos
  · exfalso; linarith
  · exact ⟨hneg.1,hneg.2,hpos⟩

namespace TerminalContacts
variable {K : Box5} {b : Vec6} {D : QuinticNumeratorInterlacing b} {q : Fin 6 → ℕ}

theorem bc_impossible (T : TerminalContacts K b D q) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : 0 < b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (R : RootBands K) (hq1 : q 1 = 2) (hq2 : q 2 = 2) (hq3 : q 3 = 3) (hq4 : q 4 = 3) : False := by
  have hb : b ≠ 0 := by intro he; simp [he] at hb0
  have h1 := T.bounds hK hwidth hb hw 1
  have h2 := T.bounds hK hwidth hb hw 2
  have h3 := T.bounds hK hwidth hb hw 3
  have h4 := T.bounds hK hwidth hb hw 4
  rw [hq1] at h1
  rw [hq2] at h2
  rw [hq3] at h3
  rw [hq4] at h4
  dsimp [QuinticNumeratorInterlacing.Bounds] at h1 h2 h3 h4
  have s1 := T.denominator_signs 1
  have s2 := T.denominator_signs 2
  have s3 := T.denominator_signs 3
  have s4 := T.denominator_signs 4
  simp only [Classification.codeAt,hq1,hq2,hq3,hq4] at s1 s2 s3 s4
  dsimp [Classification.rotated,StageSigns,phaseCorner] at s1 s2 s3 s4
  have ho1 : 0 < K.oddUpper (T.t 1) := s1.2
  have ho2 : K.oddUpper (T.t 2) < 0 := s2.2
  have ho3 : K.oddUpper (T.t 3) < 0 := s3.2
  have ho4 : 0 < K.oddUpper (T.t 4) := s4.2
  rw [R.odd_upper] at ho1 ho2 ho3 ho4
  have hαβ : R.oU < R.pL := by rcases R.ordered with ⟨_,_,_,_,h1,h2,h3,_⟩; linarith
  have h12 := quadratic_pos_neg_crossing (a := 1) zero_lt_one hαβ (T.increasing (by decide : (1:Fin 6)<2))
    (by simpa using ho1) (by simpa using ho2)
  have h34 := quadratic_neg_pos_crossing (a := 1) zero_lt_one hαβ (T.increasing (by decide : (3:Fin 6)<4))
    (by simpa using ho3) (by simpa using ho4)
  have he : 0 < D.e := lt_of_le_of_ne D.e_nonneg (fun hz => (ne_of_gt hb5) ((D.origin_iff hb1).mpr hz.symm))
  apply K.bc_terminal_contacts hK hb0 hb5 hw D R
    (r := T.t 1) (s := T.t 2) (u := T.t 3) (v := T.t 4)
  · exact ⟨he,D.e_lt_k,h1.1,h12.1,h12.2.1,h2.2,h3.1,h34.2.1,h34.2.2,h4.2⟩
  · exact T.increasing (by decide)
  · exact T.increasing (by decide)
  · simpa [hq1,phaseCorner] using T.contacts 1
  · simpa [hq2,phaseCorner] using T.contacts 2
  · simpa [hq3,phaseCorner] using T.contacts 3
  · simpa [hq4,phaseCorner] using T.contacts 4

theorem ad_impossible (T : TerminalContacts K b D q) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb0 : 0 < b 0) (hb5 : 0 < b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (R : RootBands K) (hq0 : q 0 = 0) (hq1 : q 1 = 1) (hq2 : q 2 = 1) (hq5 : q 5 = 4) : False := by
  have hb : b ≠ 0 := by intro he; simp [he] at hb0
  have h0 := T.bounds hK hwidth hb hw 0
  have h1 := T.bounds hK hwidth hb hw 1
  have h2 := T.bounds hK hwidth hb hw 2
  have h5 := T.bounds hK hwidth hb hw 5
  rw [hq0] at h0
  rw [hq1] at h1
  rw [hq2] at h2
  rw [hq5] at h5
  dsimp [QuinticNumeratorInterlacing.Bounds] at h0 h1 h2 h5
  have s1 := T.denominator_signs 1
  have s2 := T.denominator_signs 2
  have s5 := T.denominator_signs 5
  simp only [Classification.codeAt,hq1,hq2,hq5] at s1 s2 s5
  dsimp [Classification.rotated,StageSigns,phaseCorner] at s1 s2 s5
  have ho1 : 0 < K.oddLower (T.t 1) := s1.2
  have ho2 : K.oddLower (T.t 2) < 0 := s2.2
  have ho5 : K.oddLower (T.t 5) < 0 := s5.2
  rw [R.odd_lower] at ho1 ho2 ho5
  have hαβ : R.oL < R.pU := by rcases R.ordered with ⟨_,_,_,h1,h2,h3,h4,h5⟩; linarith
  have h12 := quadratic_pos_neg_crossing (a := 1) zero_lt_one hαβ (T.increasing (by decide : (1:Fin 6)<2))
    (by simpa using ho1) (by simpa using ho2)
  have hz := quadratic_negative_between (a := 1) zero_lt_one hαβ (by simpa using ho5)
  apply K.ad_terminal_contacts hK hb0 hb5 hw D R
    (w := T.t 0) (r := T.t 1) (s := T.t 2) (z := T.t 5)
  · exact ⟨T.positive 0,h0,h1.1,h12.1,h12.2.1,h2.2,D.k_lt_f,D.f_lt_l,h5,hz.2⟩
  · exact T.increasing (by decide)
  · exact T.increasing (by decide)
  · simpa [hq1,phaseCorner] using T.contacts 1
  · simpa [hq2,phaseCorner] using T.contacts 2
  · simpa [hq0,phaseCorner] using T.contacts 0
  · simpa [hq5,phaseCorner] using T.contacts 5

theorem cd_impossible (T : TerminalContacts K b D q) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : 0 < b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (R : RootBands K) (hq0 : q 0 = 0) (hq3 : q 3 = 3) (hq4 : q 4 = 3) (hq5 : q 5 = 4) : False := by
  have hb : b ≠ 0 := by intro he; simp [he] at hb0
  have h0 := T.bounds hK hwidth hb hw 0
  have h3 := T.bounds hK hwidth hb hw 3
  have h4 := T.bounds hK hwidth hb hw 4
  have h5 := T.bounds hK hwidth hb hw 5
  rw [hq0] at h0
  rw [hq3] at h3
  rw [hq4] at h4
  rw [hq5] at h5
  dsimp [QuinticNumeratorInterlacing.Bounds] at h0 h3 h4 h5
  have s0 := T.denominator_signs 0
  have s3 := T.denominator_signs 3
  have s4 := T.denominator_signs 4
  simp only [Classification.codeAt,hq0,hq3,hq4] at s0 s3 s4
  dsimp [Classification.rotated,StageSigns,phaseCorner] at s0 s3 s4
  have he0 : K.evenLower (T.t 0) < 0 := s0.1
  have he3 : K.evenLower (T.t 3) < 0 := s3.1
  have he4 : 0 < K.evenLower (T.t 4) := s4.1
  rw [R.even_lower] at he0 he3 he4
  have ha1 : 0 < K.lower.a1 := (quintic_coefficients_pos (hK _ K.lower_mem)).1
  have hαβ : R.eL < R.fU := by rcases R.ordered with ⟨_,h1,h2,h3,h4,h5,_,_⟩; linarith
  have h34 := quadratic_neg_pos_crossing ha1 hαβ (T.increasing (by decide : (3:Fin 6)<4)) he3 he4
  have hw0 := quadratic_negative_between ha1 hαβ he0
  apply K.cd_terminal_contacts hK hb0 hb1 hb5 hw D R
    (w := T.t 0) (u := T.t 3) (v := T.t 4) (z := T.t 5)
  · exact ⟨R.ordered.1,hw0.1,h0,D.e_lt_k,D.k_lt_f,h3.1,h34.2.1,h34.2.2,h4.2,h5⟩
  · exact T.increasing (by decide)
  · exact T.increasing (by decide)
  · simpa [hq3,phaseCorner] using T.contacts 3
  · simpa [hq4,phaseCorner] using T.contacts 4
  · simpa [hq0,phaseCorner] using T.contacts 0
  · simpa [hq5,phaseCorner] using T.contacts 5

end TerminalContacts
end
end SPR.N5.Direct
