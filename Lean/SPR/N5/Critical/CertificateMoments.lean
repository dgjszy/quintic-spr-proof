import SPR.N5.Critical.SupportedCertificate

/-! Exact removal of compactification, with infinity kept as a separate mass.
## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
将六维平衡恒等式展开为偶部、奇部的消失矩和无穷远质量项。
-/
namespace SPR.N5.Direct

noncomputable section
open Set

def infinityFeature : Vec6 := ![1, 0, 0, 0, 0, 0]
def finiteFrequency (x : ℝ) : ℝ := x / (1 - x)
def finiteWeight (x w : ℝ) : ℝ := w * (1 - x) ^ 5
def infiniteWeight (x w : ℝ) : ℝ := if x = 1 then w else 0

theorem compact_weight_split (a : Poly5) (x w : ℝ) :
    w • compactFeature a x = finiteWeight x w • feature a (finiteFrequency x) +
      infiniteWeight x w • infinityFeature := by
  by_cases hx : x = 1
  · simp [hx, compactFeature_at_one, finiteWeight, infiniteWeight, infinityFeature]
  · rw [compactFeature_eq a hx]
    simp only [finiteWeight, finiteFrequency, infiniteWeight, if_neg hx, zero_smul,
      add_zero, smul_smul]

theorem finiteWeight_nonneg {x w : ℝ} (hx : x ≤ 1) (hw : 0 ≤ w) :
    0 ≤ finiteWeight x w := mul_nonneg hw (pow_nonneg (sub_nonneg.mpr hx) 5)

theorem finiteWeight_pos {x w : ℝ} (hx : x < 1) (hw : 0 < w) :
    0 < finiteWeight x w := mul_pos hw (pow_pos (sub_pos.mpr hx) 5)

theorem infiniteWeight_nonneg (x : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ infiniteWeight x w := by unfold infiniteWeight; split_ifs <;> positivity

theorem finiteFrequency_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ finiteFrequency x := div_nonneg hx.1 (sub_nonneg.mpr hx.2)

theorem certificate_decompactify {n : ℕ} (a : Fin n → Poly5) (x w : Fin n → ℝ)
    (hz : (∑ i, w i • compactFeature (a i) (x i)) = 0) :
    (∑ i, finiteWeight (x i) (w i) • feature (a i) (finiteFrequency (x i))) +
      (∑ i, infiniteWeight (x i) (w i)) • infinityFeature = 0 := by
  simpa only [compact_weight_split, Finset.sum_add_distrib, ← Finset.sum_smul] using hz

/-- The six moment equations are exactly the six coordinates of a finite-frequency
certificate plus its separate nonnegative infinity mass. No distinctness or positivity
assumptions are needed for this algebraic equivalence. -/
theorem feature_certificate_iff_moments {n : ℕ} (a : Fin n → Poly5) (t μ : Fin n → ℝ)
    (μinf : ℝ) :
    ((∑ i, μ i • feature (a i) (t i)) + μinf • infinityFeature = 0) ↔
      (∑ i, μ i * evenPart (a i) (t i)) = 0 ∧
      (∑ i, μ i * (t i * evenPart (a i) (t i))) = 0 ∧
      (∑ i, μ i * ((t i) ^ 2 * evenPart (a i) (t i))) = 0 ∧
      (∑ i, μ i * (t i * oddPart (a i) (t i))) = 0 ∧
      (∑ i, μ i * ((t i) ^ 2 * oddPart (a i) (t i))) = 0 ∧
      (∑ i, μ i * ((t i) ^ 3 * oddPart (a i) (t i))) = -μinf := by
  have heq : ((∑ i, μ i • feature (a i) (t i)) + μinf • infinityFeature = 0) ↔
      ∀ j : Fin 6, ((∑ i, μ i • feature (a i) (t i)) + μinf • infinityFeature) j = 0 := by
    exact funext_iff
  rw [heq]
  simp only [Fin.forall_fin_succ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, feature, infinityFeature, Matrix.cons_val_zero, Matrix.cons_val_succ,
    mul_one, mul_zero, add_zero, mul_neg, Finset.sum_neg_distrib, neg_eq_zero,
    Fin.forall_fin_zero, and_true]
  constructor <;> intro h <;> rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  · exact ⟨h5, h3, h1, h4, h2, by linarith⟩
  · exact ⟨by linarith, h2, h4, h1, h3, h0⟩

theorem positive_finite_contact_of_compact {a : Poly5} {b : Vec6} {x : ℝ}
    (hx : x < 1) (hcontact : dot6 b (compactFeature a x) = 0) :
    generalPairing a b (finiteFrequency x) = 0 := by
  rw [compact_pairing_eq a b (ne_of_lt hx)] at hcontact
  exact (mul_eq_zero.mp hcontact).resolve_left (ne_of_gt (pow_pos (sub_pos.mpr hx) 5))

theorem infinity_contact_leading_zero {a : Poly5} {b : Vec6}
    (hcontact : dot6 b (compactFeature a 1) = 0) : b 0 = 0 := by
  simpa only [dot6_at_infinity] using hcontact

/-- A normalized zero certificate cannot be supported only at infinity. -/
theorem certificate_has_finite_point {n : ℕ} (a : Fin n → Poly5) (x w : Fin n → ℝ)
    (hx : ∀ i, x i ≤ 1) (hw : (∑ i, w i) = 1)
    (hz : (∑ i, w i • compactFeature (a i) (x i)) = 0) :
    ∃ i, x i < 1 := by
  by_contra h
  have hall : ∀ i, x i = 1 := by
    intro i
    have hi : ¬ x i < 1 := fun hi => h ⟨i, hi⟩
    exact le_antisymm (hx i) (le_of_not_gt hi)
  simp only [hall, compactFeature_at_one, ← Finset.sum_smul, hw, one_smul] at hz
  have he := congrArg (fun v : Vec6 => v 0) hz
  norm_num at he

theorem certificate_infinity_complementarity {n : ℕ} (a : Fin n → Poly5)
    (b : Vec6) (x w : Fin n → ℝ)
    (hc : ∀ i, dot6 b (compactFeature (a i) (x i)) = 0) :
    (∑ i, infiniteWeight (x i) (w i)) * b 0 = 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : x i = 1
  · have hb : b 0 = 0 := infinity_contact_leading_zero (hi ▸ hc i)
    simp [hb]
  · simp [infiniteWeight, hi]

theorem certificate_finite_contacts {n : ℕ} (a : Fin n → Poly5)
    (b : Vec6) (x w : Fin n → ℝ) (hx : ∀ i, x i ≤ 1)
    (hc : ∀ i, dot6 b (compactFeature (a i) (x i)) = 0) :
    ∀ i, 0 < finiteWeight (x i) (w i) →
      generalPairing (a i) b (finiteFrequency (x i)) = 0 := by
  intro i hi
  have hxi : x i < 1 := lt_of_le_of_ne (hx i) (by
    intro he
    simp [finiteWeight, he] at hi)
  exact positive_finite_contact_of_compact hxi (hc i)

/-- Keeping infinity separately does not increase the number of active atoms. -/
theorem certificate_support_count {n : ℕ} (x w : Fin n → ℝ) :
    (Finset.univ.filter (fun i => 0 < finiteWeight (x i) (w i))).card +
      (if 0 < ∑ i, infiniteWeight (x i) (w i) then 1 else 0) ≤ n := by
  classical
  by_cases hm : 0 < ∑ i, infiniteWeight (x i) (w i)
  · simp only [if_pos hm]
    have hex : ∃ i, x i = 1 := by
      by_contra h
      have hall : ∀ i, x i ≠ 1 := fun i hi => h ⟨i, hi⟩
      simp [infiniteWeight, hall] at hm
    obtain ⟨i, hi⟩ := hex
    have hsub : Finset.univ.filter (fun j => 0 < finiteWeight (x j) (w j)) ⊆
        Finset.univ.erase i := by
      intro j hj
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
      intro he
      subst j
      have hp := (Finset.mem_filter.mp hj).2
      simp [finiteWeight, hi] at hp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] at hcard
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    omega
  · simpa only [if_neg hm, add_zero, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset
        (fun i => 0 < finiteWeight (x i) (w i)) Finset.univ)

end
end SPR.N5.Direct
