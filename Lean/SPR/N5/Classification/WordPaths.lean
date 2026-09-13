import SPR.N5.Contacts.ContactSigns

/-!
# WordPaths

论文 §5 与附录 A：必要候选表的完备性及基本排除。
将逐节点的符号与单调区域序列转换为候选判定中的列表路径。
-/

namespace SPR.N5.Direct
noncomputable section

namespace Classification

theorem zonePath_ofFn {n : ℕ} (s z : Fin n → ℕ) (hz : Monotone z)
    (hs : ∀ i, z i ∈ zones (s i)) {lo : ℕ} (hlo : ∀ i, lo ≤ z i) :
    ZonePath lo (List.ofFn s) := by
  induction n generalizing lo with
  | zero => simpa using ZonePath.nil lo
  | succ n ih =>
    rw [List.ofFn_succ]
    apply ZonePath.cons (z 0) (hs 0) (hlo 0)
    exact ih (fun i => s i.succ) (fun i => z i.succ)
      (fun i j hij => hz (Fin.succ_le_succ_iff.mpr hij))
      (fun i => hs i.succ) (fun i => hz (Fin.zero_le i.succ))

theorem orderedWord_ofFn {n : ℕ} (s : Fin n → ℕ) (hs : Monotone s)
    {lo hi : ℕ} (hl : ∀ i, lo ≤ s i) (hh : ∀ i, s i < hi) :
    OrderedWord lo hi (List.ofFn s) := by
  induction n generalizing lo with
  | zero => simp [OrderedWord]
  | succ n ih =>
    rw [List.ofFn_succ]
    exact ⟨hl 0,hh 0,ih (fun i => s i.succ)
      (fun i j hij => hs (Fin.succ_le_succ_iff.mpr hij))
      (fun i => hs (Fin.zero_le i.succ)) (fun i => hh i.succ)⟩

end Classification

/-- Convert the alternating-power sign condition into a sign for c times eta. -/
theorem signed_weight_product {m : ℕ} {η c : ℝ}
    (hη : 0 < (-1 : ℝ)^m * η) (hc : c ≠ 0) :
    if (((m % 2 == 1) != (c < 0)) : Bool) then c*η < 0 else 0 < c*η := by
  rw [neg_one_pow_eq_pow_mod_two] at hη
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with hm | hm <;> by_cases hn : c < 0 <;>
    simp [hm,hn] at hη ⊢
  · exact mul_neg_of_neg_of_pos hn hη
  · exact mul_pos (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hc)) hη
  · exact mul_pos_of_neg_of_neg hn (by linarith)
  · exact mul_neg_of_pos_of_neg (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hc)) (by linarith)

end
end SPR.N5.Direct
