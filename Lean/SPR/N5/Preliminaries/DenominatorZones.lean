import SPR.N5.Preliminaries.RootBands
import SPR.N5.Classification.Classification

/-!
# DenominatorZones

论文 §2：Hurwitz 稳定性、零点交错及统一分母零点区间。
将分母零点区间及间隙编号，连接实际分母符号与分类所用区域路径。
-/

namespace SPR.N5.Direct
noncomputable section

namespace RootBands
variable {K : Box5}

def zone (D : RootBands K) (t : ℝ) : ℕ :=
  if t ≤ D.eL then 0 else if t ≤ D.eU then 1 else
  if t ≤ D.oL then 2 else if t ≤ D.oU then 3 else
  if t ≤ D.fL then 4 else if t ≤ D.fU then 5 else
  if t ≤ D.pL then 6 else if t ≤ D.pU then 7 else 8

set_option maxHeartbeats 800000 in
theorem zone_monotone (D : RootBands K) : Monotone D.zone := by
  intro x y hxy
  unfold zone
  split_ifs
  all_goals first | omega | (exfalso; linarith)

theorem sign_bounds (D : RootBands K) (hK : K.RobustlyHurwitz)
    {a : Poly5} (ha : K.Contains a) {t : ℝ} (ht : 0 ≤ t) :
    (0 < evenPart a t → t < D.eU ∨ D.fL < t) ∧
    (evenPart a t < 0 → D.eL < t ∧ t < D.fU) ∧
    (0 < oddPart a t → t < D.oU ∨ D.pL < t) ∧
    (oddPart a t < 0 → D.oL < t ∧ t < D.pU) := by
  obtain ⟨hel,heu,hol,hou⟩ := K.component_bounds ha ht
  have ha1 : 0 < K.upper.a1 := (quintic_coefficients_pos (hK _ (K.corner_mem .A))).1
  have hl1 : 0 < K.lower.a1 := (quintic_coefficients_pos (hK _ (K.corner_mem .C))).1
  rcases D.ordered with ⟨he,hee,heo,hoo,hof,hff,hfp,hpp⟩
  rw [D.even_lower] at hel
  rw [D.even_upper] at heu
  rw [D.odd_lower] at hol
  rw [D.odd_upper] at hou
  constructor
  · intro hp
    by_contra hn
    push_neg at hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn.1) (sub_nonpos.mpr hn.2)
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha1.le hm)) (hp.trans_le heu)
  constructor
  · intro hn
    exact quadratic_negative_between hl1 (by linarith) (hel.trans_lt hn)
  constructor
  · intro hp
    by_contra hn
    push_neg at hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn.1) (sub_nonpos.mpr hn.2)
    exact (not_lt_of_ge hm) (hp.trans_le hou)
  · intro hn
    exact quadratic_negative_between (a := 1) zero_lt_one (by linarith)
      (by simpa using hol.trans_lt hn)

set_option maxHeartbeats 800000 in
theorem zone_pp (D : RootBands K) {t : ℝ}
    (hE : t < D.eU ∨ D.fL < t) (hO : t < D.oU ∨ D.pL < t) :
    D.zone t ∈ Classification.zones 0 := by
  rcases D.ordered with ⟨he,hee,heo,hoo,hof,hff,hfp,hpp⟩
  rcases hE with hE | hE <;> rcases hO with hO | hO <;>
    unfold zone <;> split_ifs <;> norm_num [Classification.zones] <;> linarith

set_option maxHeartbeats 800000 in
theorem zone_np (D : RootBands K) {t : ℝ}
    (hE : D.eL < t ∧ t < D.fU) (hO : t < D.oU ∨ D.pL < t) :
    D.zone t ∈ Classification.zones 1 := by
  rcases D.ordered with ⟨he,hee,heo,hoo,hof,hff,hfp,hpp⟩
  rcases hE with ⟨hEl,hEu⟩
  rcases hO with hO | hO <;>
    unfold zone <;> split_ifs <;> norm_num [Classification.zones] <;> linarith

set_option maxHeartbeats 800000 in
theorem zone_nn (D : RootBands K) {t : ℝ}
    (hE : D.eL < t ∧ t < D.fU) (hO : D.oL < t ∧ t < D.pU) :
    D.zone t ∈ Classification.zones 2 := by
  rcases D.ordered with ⟨he,hee,heo,hoo,hof,hff,hfp,hpp⟩
  rcases hE with ⟨hEl,hEu⟩
  rcases hO with ⟨hOl,hOu⟩
  unfold zone
  split_ifs <;> norm_num [Classification.zones] <;> linarith

set_option maxHeartbeats 800000 in
theorem zone_pn (D : RootBands K) {t : ℝ}
    (hE : t < D.eU ∨ D.fL < t) (hO : D.oL < t ∧ t < D.pU) :
    D.zone t ∈ Classification.zones 3 := by
  rcases D.ordered with ⟨he,hee,heo,hoo,hof,hff,hfp,hpp⟩
  rcases hO with ⟨hOl,hOu⟩
  rcases hE with hE | hE <;>
    unfold zone <;> split_ifs <;> norm_num [Classification.zones] <;> linarith

end RootBands
end
end SPR.N5.Direct
