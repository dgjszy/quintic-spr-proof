import SPR.N5.Contacts.NumeratorPhases
import SPR.N5.Preliminaries.DenominatorZones

/-!
# ContactSigns

论文 §5：接触点重数、符号和极小顶点之间的联系。
按常数倍恒等式旋转分子符号，得到各节点处的分母符号。
-/

namespace SPR.N5.Direct
noncomputable section

theorem stageSigns_positive_scaling {s : ℕ} (hs : s < 5) {E O p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) : StageSigns s (p*E) (q*O) ↔ StageSigns s E O := by
  have hpn : ¬ p < 0 := not_lt_of_ge hp.le
  have hqn : ¬ q < 0 := not_lt_of_ge hq.le
  interval_cases s <;> simp [StageSigns,mul_pos_iff,mul_neg_iff,hp,hq,hpn,hqn]

theorem stageSigns_rotated {s : ℕ} (hs : s < 5) {E O σ : ℝ}
    (h : StageSigns s E O) (hσ : 0 < σ) :
    StageSigns (Classification.rotated s) (σ*O) (-(σ*E)) := by
  have hn : ¬ σ < 0 := not_lt_of_ge hσ.le
  interval_cases s <;>
    simp_all [StageSigns,Classification.rotated,mul_pos_iff,mul_neg_iff]

theorem stageSigns_rotated_negative {s : ℕ} (hs : s < 5) {E O σ : ℝ}
    (h : StageSigns s E O) (hσ : σ < 0) :
    StageSigns ((Classification.rotated s+2)%4) (σ*O) (-(σ*E)) := by
  have hn : ¬ 0 < σ := not_lt_of_ge hσ.le
  interval_cases s <;>
    simp_all [StageSigns,Classification.rotated,mul_pos_iff,mul_neg_iff]

theorem contact_stageSigns {s : ℕ} (hs : s < 5) {E O A B μ t σ : ℝ}
    (h : StageSigns s E O) (hμ : 0 < μ) (ht : 0 < t)
    (hA : μ*A = σ*O) (hB : μ*(t*B) = -(σ*E)) :
    (0 < σ → StageSigns (Classification.rotated s) A B) ∧
    (σ < 0 → StageSigns ((Classification.rotated s+2)%4) A B) := by
  have hr : Classification.rotated s < 5 := by
    interval_cases s <;> norm_num [Classification.rotated]
  have hm : (Classification.rotated s+2)%4 < 5 := (Nat.mod_lt _ (by decide)).trans (by decide)
  have hB' : (μ*t)*B = -(σ*E) := by rw [mul_assoc,hB]
  constructor
  · intro hσ
    apply (stageSigns_positive_scaling hr hμ (mul_pos hμ ht)).mp
    rw [hA,hB']
    exact stageSigns_rotated hs h hσ
  · intro hσ
    apply (stageSigns_positive_scaling hm hμ (mul_pos hμ ht)).mp
    rw [hA,hB']
    exact stageSigns_rotated_negative hs h hσ

theorem RootBands.stageSigns_zone {K : Box5} (D : RootBands K) (hK : K.RobustlyHurwitz)
    {a : Poly5} (ha : K.Contains a) {t : ℝ} (ht : 0 ≤ t) {s : ℕ} (hs : s < 4)
    (h : StageSigns s (evenPart a t) (oddPart a t)) :
    D.zone t ∈ Classification.zones s := by
  obtain ⟨hEp,hEn,hOp,hOn⟩ := D.sign_bounds hK ha ht
  interval_cases s
  · exact D.zone_pp (hEp h.1) (hOp h.2)
  · exact D.zone_np (hEn h.1) (hOp h.2)
  · exact D.zone_nn (hEn h.1) (hOn h.2)
  · exact D.zone_pn (hEp h.1) (hOn h.2)

end
end SPR.N5.Direct
