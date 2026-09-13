import SPR.N5.Interpolation.OrderedWeights

/-!
# NumeratorPhases

论文 §5：接触点重数、符号和极小顶点之间的联系。
用分子零点划分的区间编号记录符号；此编号不同于分母区域编号。
-/

namespace SPR.N5.Direct
noncomputable section
open Polynomial

/-- Codes 0,1,2,3,4 carry signs ++,-+,--,+-,++ respectively. -/
def StageSigns (s : ℕ) (E O : ℝ) : Prop :=
  match s with
  | 0 => 0 < E ∧ 0 < O
  | 1 => E < 0 ∧ 0 < O
  | 2 => E < 0 ∧ O < 0
  | 3 => 0 < E ∧ O < 0
  | 4 => 0 < E ∧ 0 < O
  | _ => False

theorem quadratic_positive_iff {a r s t : ℝ} (ha : 0 < a) (hrs : r < s) :
    0 < a * ((t-r)*(t-s)) ↔ t < r ∨ s < t := by
  rw [mul_pos_iff_of_pos_left ha,mul_pos_iff]
  constructor
  · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact Or.inr (sub_pos.mp h2)
    · exact Or.inl (sub_neg.mp h1)
  · rintro (h | h)
    · exact Or.inr ⟨sub_neg.mpr h,sub_neg.mpr (h.trans hrs)⟩
    · exact Or.inl ⟨sub_pos.mpr (hrs.trans h),sub_pos.mpr h⟩

theorem quadratic_negative_of_between {a r s t : ℝ} (ha : 0 < a)
    (hr : r < t) (hs : t < s) : a * ((t-r)*(t-s)) < 0 :=
  mul_neg_of_pos_of_neg ha (mul_neg_of_pos_of_neg (sub_pos.mpr hr) (sub_neg.mpr hs))

namespace QuinticNumeratorInterlacing
variable {b : Vec6}
def phase (D : QuinticNumeratorInterlacing b) (t : ℝ) : ℕ :=
  if t < D.e then 0 else if t < D.k then 1 else if t < D.f then 2 else if t < D.l then 3 else 4

theorem phase_monotone (D : QuinticNumeratorInterlacing b) : Monotone D.phase := by
  intro x y hxy
  unfold phase
  split_ifs
  all_goals first | omega | (exfalso;linarith)

theorem phase_lt (D : QuinticNumeratorInterlacing b) (t : ℝ) : D.phase t < 5 := by
  unfold phase
  split_ifs <;> omega

theorem component_values (D : QuinticNumeratorInterlacing b) (t : ℝ) :
    numeratorEven b t = b 1 * ((t-D.e)*(t-D.f)) ∧
    numeratorOdd b t = b 0 * ((t-D.k)*(t-D.l)) := by
  constructor
  · have h := congrArg (fun p : ℝ[X] => p.eval t) D.even_factor
    simpa only [numeratorEvenPoly_eval,eval_mul,eval_C,eval_sub,eval_X] using h
  · have h := congrArg (fun p : ℝ[X] => p.eval t) D.odd_factor
    simpa only [numeratorOddPoly_eval,eval_mul,eval_C,eval_sub,eval_X] using h

theorem phase_signs (D : QuinticNumeratorInterlacing b) (hb0 : 0 < b 0) (hb1 : 0 < b 1)
    {t : ℝ} (hE : numeratorEven b t ≠ 0) (hO : numeratorOdd b t ≠ 0) :
    StageSigns (D.phase t) (numeratorEven b t) (numeratorOdd b t) := by
  obtain ⟨hEv,hOv⟩ := D.component_values t
  have hte : t ≠ D.e := by intro he; rw [hEv,he] at hE; simp at hE
  have htf : t ≠ D.f := by intro he; rw [hEv,he] at hE; simp at hE
  have htk : t ≠ D.k := by intro he; rw [hOv,he] at hO; simp at hO
  have htl : t ≠ D.l := by intro he; rw [hOv,he] at hO; simp at hO
  have hek := D.e_lt_k
  have hkf := D.k_lt_f
  have hfl := D.f_lt_l
  have hEP := quadratic_positive_iff (t := t) hb1 (hek.trans hkf)
  have hOP := quadratic_positive_iff (t := t) hb0 (hkf.trans hfl)
  unfold phase
  split_ifs with he hk hf hl
  · exact ⟨hEv ▸ (hEP.mpr (Or.inl he)),hOv ▸ (hOP.mpr (Or.inl (he.trans hek)))⟩
  · have het : D.e < t := lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hte)
    exact ⟨hEv ▸ quadratic_negative_of_between hb1 het (hk.trans hkf),
      hOv ▸ hOP.mpr (Or.inl hk)⟩
  · have hkt : D.k < t := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm htk)
    exact ⟨hEv ▸ quadratic_negative_of_between hb1 (hek.trans hkt) hf,
      hOv ▸ quadratic_negative_of_between hb0 hkt (hf.trans hfl)⟩
  · have hft : D.f < t := lt_of_le_of_ne (le_of_not_gt hf) (Ne.symm htf)
    exact ⟨hEv ▸ hEP.mpr (Or.inr hft),
      hOv ▸ quadratic_negative_of_between hb0 (hkf.trans hft) hl⟩
  · have hlt : D.l < t := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm htl)
    exact ⟨hEv ▸ hEP.mpr (Or.inr (hfl.trans hlt)),hOv ▸ hOP.mpr (Or.inr hlt)⟩

theorem phase_pos_of_origin (D : QuinticNumeratorInterlacing b) (he : D.e = 0)
    {t : ℝ} (ht : 0 ≤ t) : 1 ≤ D.phase t := by
  unfold phase
  rw [he,if_neg (not_lt_of_ge ht)]
  split_ifs <;> omega

end QuinticNumeratorInterlacing
namespace QuarticNumeratorInterlacing
variable {b : Vec6}
def phase (D : QuarticNumeratorInterlacing b) (t : ℝ) : ℕ :=
  if t < D.e then 0 else if t < D.k then 1 else if t < D.f then 2 else 3

theorem phase_monotone (D : QuarticNumeratorInterlacing b) : Monotone D.phase := by
  intro x y hxy
  unfold phase
  split_ifs
  all_goals first | omega | (exfalso;linarith)

theorem phase_lt (D : QuarticNumeratorInterlacing b) (t : ℝ) : D.phase t < 4 := by
  unfold phase
  split_ifs <;> omega

theorem component_values (D : QuarticNumeratorInterlacing b) (t : ℝ) :
    numeratorEven b t = b 1 * ((t-D.e)*(t-D.f)) ∧
    numeratorOdd b t = b 2 * (D.k-t) := by
  constructor
  · have h := congrArg (fun p : ℝ[X] => p.eval t) D.even_factor
    simpa only [numeratorEvenPoly_eval,eval_mul,eval_C,eval_sub,eval_X] using h
  · have h := congrArg (fun p : ℝ[X] => p.eval t) D.odd_factor
    simp only [numeratorOddPoly_eval,eval_mul,eval_C,eval_sub,eval_X] at h
    linarith

theorem phase_signs (D : QuarticNumeratorInterlacing b) (hb1 : 0 < b 1) (hb2 : 0 < b 2)
    {t : ℝ} (hE : numeratorEven b t ≠ 0) (hO : numeratorOdd b t ≠ 0) :
    StageSigns (D.phase t) (numeratorEven b t) (numeratorOdd b t) := by
  obtain ⟨hEv,hOv⟩ := D.component_values t
  have hte : t ≠ D.e := by intro he; rw [hEv,he] at hE; simp at hE
  have htf : t ≠ D.f := by intro he; rw [hEv,he] at hE; simp at hE
  have htk : t ≠ D.k := by intro he; rw [hOv,he] at hO; simp at hO
  have hek := D.e_lt_k
  have hkf := D.k_lt_f
  have hEP := quadratic_positive_iff (t := t) hb1 (hek.trans hkf)
  unfold phase
  split_ifs with he hk hf
  · exact ⟨hEv ▸ hEP.mpr (Or.inl he),
      hOv ▸ mul_pos hb2 (sub_pos.mpr (he.trans hek))⟩
  · have het : D.e < t := lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hte)
    exact ⟨hEv ▸ quadratic_negative_of_between hb1 het (hk.trans hkf),
      hOv ▸ mul_pos hb2 (sub_pos.mpr hk)⟩
  · have hkt : D.k < t := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm htk)
    exact ⟨hEv ▸ quadratic_negative_of_between hb1 (hek.trans hkt) hf,
      hOv ▸ mul_neg_of_pos_of_neg hb2 (sub_neg.mpr hkt)⟩
  · have hft : D.f < t := lt_of_le_of_ne (le_of_not_gt hf) (Ne.symm htf)
    exact ⟨hEv ▸ hEP.mpr (Or.inr hft),
      hOv ▸ mul_neg_of_pos_of_neg hb2 (sub_neg.mpr (hkf.trans hft))⟩

theorem phase_pos_of_origin (D : QuarticNumeratorInterlacing b) (he : D.e = 0)
    {t : ℝ} (ht : 0 ≤ t) : 1 ≤ D.phase t := by
  unfold phase
  rw [he,if_neg (not_lt_of_ge ht)]
  split_ifs <;> omega

end QuarticNumeratorInterlacing

end
end SPR.N5.Direct
