import SPR.N5.Critical.FiniteHull

/-! Six points suffice on a nonzero supporting hyperplane.
This replaces the need for a connected-set Caratheodory sharpening at the critical box.
The existence of the critical box and its supporting vector is not assumed as an axiom.

## 与论文的对应

论文 §3：稳定扩张、临界参数、有限凸表示与矩等式。
在非零法向量的核中选择有限表示，得到至多六点的支持界。
-/
namespace SPR.N5.Direct

noncomputable section
open Set

theorem positive_combination_contacts {ι : Type*} [Fintype ι]
    (f : Vec6 →L[ℝ] ℝ) (z : ι → Vec6) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hf : ∀ i, 0 ≤ f (z i))
    (hz : (∑ i, w i • z i) = 0) : ∀ i, f (z i) = 0 := by
  have hsum : (∑ i, w i * f (z i)) = 0 := by
    have h := congrArg f hz
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using h
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hw i).le (hf i))).mp hsum
  intro i
  exact (mul_eq_zero.mp (hterms i (Finset.mem_univ i))).resolve_left (ne_of_gt (hw i))

theorem affineIndependent_card_le_six_of_annihilator {ι : Type*} [Fintype ι]
    {z : ι → Vec6} (hz : AffineIndependent ℝ z)
    (f : Vec6 →L[ℝ] ℝ) (hf : f ≠ 0) (hzero : ∀ i, f (z i) = 0) :
    Fintype.card ι ≤ 6 := by
  have h7 := affineIndependent_card_le_seven hz
  by_contra h6
  have hcard : Fintype.card ι = Module.finrank ℝ Vec6 + 1 := by
    have hdim : Module.finrank ℝ Vec6 = 6 := by simp [Vec6]
    omega
  have hspan := hz.vectorSpan_eq_top_of_card_eq_finrank_add_one hcard
  have hle : vectorSpan ℝ (Set.range z) ≤ LinearMap.ker f.toLinearMap := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
    change f (z i - z j) = 0
    rw [map_sub, hzero i, hzero j, sub_self]
  rw [hspan] at hle
  have hlinear : f.toLinearMap = 0 := LinearMap.ker_eq_top.mp (top_unique hle)
  apply hf
  ext v
  exact congrArg (fun g : Vec6 →ₗ[ℝ] ℝ => g v) hlinear

theorem supported_six_point_representation {S : Set Vec6} (hS : IsCompact S)
    (hzero : (0 : Vec6) ∈ closedConvexHull ℝ S)
    (f : Vec6 →L[ℝ] ℝ) (hf : f ≠ 0) (hpos : ∀ z ∈ S, 0 ≤ f z) :
    ∃ n : ℕ, n ≤ 6 ∧ ∃ (z : Fin n → Vec6) (w : Fin n → ℝ),
      (∀ i, z i ∈ S) ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • z i) = 0 ∧ ∀ i, f (z i) = 0 := by
  rw [closedConvexHull_eq_convexHull_six hS] at hzero
  obtain ⟨n, _, z, w, hz, hind, hw, hsum, hcomb⟩ := finite_convex_representation hzero
  have hcontacts := positive_combination_contacts f z w hw (fun i => hpos _ (hz i)) hcomb
  have hn := affineIndependent_card_le_six_of_annihilator hind f hf hcontacts
  exact ⟨n, by simpa using hn, z, w, hz, hind, hw, hsum, hcomb, hcontacts⟩

theorem dot6CLM_ne_zero {b : Vec6} (hb : b ≠ 0) : dot6CLM b ≠ 0 := by
  intro h
  apply hb
  ext i
  have he := congrArg (fun f : Vec6 →L[ℝ] ℝ => f (Pi.single i 1)) h
  simpa [dot6CLM_apply, dot6, Pi.single_apply, mul_ite] using he

theorem compact_pairing_nonneg (a : Poly5) (b : Vec6) (hb : 0 ≤ b 0)
    (hpair : ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ dot6 b (compactFeature a x) := by
  by_cases hx1 : x = 1
  · simpa only [hx1, dot6_at_infinity] using hb
  · rw [compact_pairing_eq a b hx1]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) 5)
      (hpair _ (div_nonneg hx.1 (sub_nonneg.mpr hx.2)))

theorem compact_pairing_nonneg_iff (a : Poly5) (b : Vec6) :
    (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ dot6 b (compactFeature a x)) ↔
      0 ≤ b 0 ∧ ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t := by
  constructor
  · intro h
    refine ⟨by simpa only [dot6_at_infinity] using h 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
    intro t ht
    have hd : 0 < 1 + t := by linarith
    have hx : t / (1 + t) < 1 := (div_lt_one hd).mpr (by linarith)
    have hc := h (t / (1 + t)) ⟨div_nonneg ht hd.le, hx.le⟩
    rw [compact_pairing_eq a b (ne_of_lt hx)] at hc
    have hid : t / (1 + t) / (1 - t / (1 + t)) = t := by field_simp; ring
    rw [hid] at hc
    exact (mul_nonneg_iff_of_pos_left (pow_pos (sub_pos.mpr hx) 5)).mp hc
  · rintro ⟨hb, hpair⟩ x hx
    exact compact_pairing_nonneg a b hb hpair hx

/-- The six-point certificate is explicit in corners and compactified frequencies.
Nonzero weak support is an explicit hypothesis here; `CriticalSupport.lean`
obtains it from the original infeasibility assumption. -/
theorem Box5.supported_six_point_certificate (K : Box5)
    (hzero : (0 : Vec6) ∈ K.featureHull) (b : Vec6) (hb : b ≠ 0) (hb0 : 0 ≤ b 0)
    (hweak : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t) :
    ∃ n : ℕ, n ≤ 6 ∧ ∃ (c : Fin n → Corner) (x w : Fin n → ℝ),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
        (∑ i, w i • compactFeature (K.corner (c i)) (x i)) = 0 ∧
        ∀ i, dot6 b (compactFeature (K.corner (c i)) (x i)) = 0 := by
  have hpos : ∀ z ∈ K.featureSet, 0 ≤ dot6CLM b z := by
    rintro z hz
    obtain ⟨c, x, hx, rfl⟩ := mem_iUnion.mp hz
    rw [dot6CLM_apply]
    exact compact_pairing_nonneg _ b hb0 (hweak _ (K.corner_mem c)) hx
  obtain ⟨n, hn, z, w, hz, _, hw, hsum, hcomb, hcontacts⟩ :=
    supported_six_point_representation K.compact_featureSet hzero
      (dot6CLM b) (dot6CLM_ne_zero hb) hpos
  have hz' : ∀ i, ∃ c : Corner, ∃ x ∈ Icc (0 : ℝ) 1, compactFeature (K.corner c) x = z i := by
    intro i
    exact mem_iUnion.mp (hz i)
  choose c x hx heq using hz'
  refine ⟨n, hn, c, x, w, hx, hw, hsum, ?_, ?_⟩
  · simpa only [heq] using hcomb
  · intro i
    rw [heq, ← dot6CLM_apply]
    exact hcontacts i

end
end SPR.N5.Direct
