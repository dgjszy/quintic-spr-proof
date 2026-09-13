import SPR.N5.Comparisons.NormalizedContacts

/-!
# TerminalContactBridges

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
从实际顶点配对提取公共取值比，使条件比值引理适用于原问题。
-/

namespace SPR.N5.Direct
noncomputable section

namespace Box5
variable (K : Box5) (hK : K.RobustlyHurwitz) {b : Vec6}
    (hb0 : 0 < b 0) (hb5 : 0 < b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (D : QuinticNumeratorInterlacing b) (R : RootBands K)

include hK hb0 hb5 hw in
theorem bc_terminal_contacts {r s u v : ℝ}
    (ho : 0 < D.e ∧ D.e < D.k ∧ D.k < r ∧ r < R.oU ∧ R.oU < s ∧ s < D.f ∧
      D.f < u ∧ u < R.pL ∧ R.pL < v ∧ v < D.l)
    (hrs : r < s) (huv : u < v)
    (hBr : generalPairing (K.corner .B) b r = 0) (hBs : generalPairing (K.corner .B) b s = 0)
    (hCu : generalPairing (K.corner .C) b u = 0) (hCv : generalPairing (K.corner .C) b v = 0) : False := by
  have hr : 0 < r := ho.1.trans (ho.2.1.trans ho.2.2.1)
  have hu : 0 < u := hr.trans (hrs.trans (ho.2.2.2.2.2.1.trans ho.2.2.2.2.2.2.1))
  obtain ⟨dB,hdB,hB⟩ := stable_normalized_doubleContact (hK _ (K.corner_mem .B)) hb0 hb5
    (hw _ (K.corner_mem .B)) hr hrs hBr hBs
  obtain ⟨dC,hdC,hC⟩ := stable_normalized_doubleContact (hK _ (K.corner_mem .C)) hb0 hb5
    (hw _ (K.corner_mem .C)) hu huv hCu hCv
  have hBe (t : ℝ) (ht : t = D.e ∨ t = D.f) :
      doubleContact r s dB t = oddProduct D.k D.l R.oU R.pL t :=
    mul_left_cancel₀ (ne_of_gt hb0) ((hB t).symm.trans
      (K.pairing_at_even_root_odd_upper D R ht .B (Or.inl rfl)))
  have hCe (t : ℝ) (ht : t = D.e ∨ t = D.f) :
      doubleContact u v dC t = oddProduct D.k D.l R.oU R.pL t :=
    mul_left_cancel₀ (ne_of_gt hb0) ((hC t).symm.trans
      (K.pairing_at_even_root_odd_upper D R ht .C (Or.inr rfl)))
  apply bc_contact_impossible ho hdB hdC
  · rw [hBe _ (Or.inl rfl),hBe _ (Or.inr rfl),hCe _ (Or.inl rfl),hCe _ (Or.inr rfl)]
  · rw [hBe _ (Or.inl rfl),hBe _ (Or.inr rfl)]

include hK hb0 hb5 hw in
theorem ad_terminal_contacts {w r s z : ℝ}
    (ho : 0 < w ∧ w < D.e ∧ D.e < r ∧ r < R.oL ∧ R.oL < s ∧ s < D.k ∧
      D.k < D.f ∧ D.f < D.l ∧ D.l < z ∧ z < R.pU)
    (hrs : r < s) (hwz : w < z)
    (hAr : generalPairing (K.corner .A) b r = 0) (hAs : generalPairing (K.corner .A) b s = 0)
    (hDw : generalPairing (K.corner .D) b w = 0) (hDz : generalPairing (K.corner .D) b z = 0) : False := by
  have hr : 0 < r := ho.1.trans (ho.2.1.trans ho.2.2.1)
  obtain ⟨dA,hdA,hA⟩ := stable_normalized_doubleContact (hK _ (K.corner_mem .A)) hb0 hb5
    (hw _ (K.corner_mem .A)) hr hrs hAr hAs
  obtain ⟨dD,hdD,hD⟩ := stable_normalized_doubleContact (hK _ (K.corner_mem .D)) hb0 hb5
    (hw _ (K.corner_mem .D)) ho.1 hwz hDw hDz
  have hAe (t : ℝ) (ht : t = D.e ∨ t = D.f) :
      doubleContact r s dA t = oddProduct D.k D.l R.oL R.pU t :=
    mul_left_cancel₀ (ne_of_gt hb0) ((hA t).symm.trans
      (K.pairing_at_even_root_odd_lower D R ht .A (Or.inl rfl)))
  have hDe (t : ℝ) (ht : t = D.e ∨ t = D.f) :
      doubleContact w z dD t = oddProduct D.k D.l R.oL R.pU t :=
    mul_left_cancel₀ (ne_of_gt hb0) ((hD t).symm.trans
      (K.pairing_at_even_root_odd_lower D R ht .D (Or.inr rfl)))
  apply ad_contact_impossible ho hdA hdD
  · rw [hAe _ (Or.inl rfl),hAe _ (Or.inr rfl),hDe _ (Or.inl rfl),hDe _ (Or.inr rfl)]
  · rw [hAe _ (Or.inl rfl),hAe _ (Or.inr rfl)]

end Box5

theorem scaled_values_ratio {a d x y u v : ℝ} (ha : a ≠ 0) (hd : d ≠ 0)
    (hx : a*x = d*u) (hy : a*y = d*v) : x/y = u/v := by
  have hxx : x = (d/a)*u := by apply (mul_left_cancel₀ ha); field_simp; nlinarith [hx]
  have hyy : y = (d/a)*v := by apply (mul_left_cancel₀ ha); field_simp; nlinarith [hy]
  rw [hxx,hyy,mul_div_mul_left _ _ (div_ne_zero hd ha)]

theorem Box5.cd_terminal_contacts (K : Box5) (hK : K.RobustlyHurwitz) {b : Vec6}
    (hb0 : 0 < b 0) (hb1 : 0 < b 1) (hb5 : 0 < b 5)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    (D : QuinticNumeratorInterlacing b) (R : RootBands K) {w u v z : ℝ}
    (ho : 0 < R.eL ∧ R.eL < w ∧ w < D.e ∧ D.e < D.k ∧ D.k < D.f ∧
      D.f < u ∧ u < R.fU ∧ R.fU < v ∧ v < D.l ∧ D.l < z)
    (huv : u < v) (hwz : w < z)
    (hCu : generalPairing (K.corner .C) b u = 0) (hCv : generalPairing (K.corner .C) b v = 0)
    (hDw : generalPairing (K.corner .D) b w = 0) (hDz : generalPairing (K.corner .D) b z = 0) : False := by
  have hord := ho
  rcases hord with ⟨hα,hαw,hwe,hek,hkf,hfu,huβ,hβv,hvl,hlz⟩
  have hu : 0 < u := by linarith
  have hw0 : 0 < w := by linarith
  obtain ⟨dC,hdC,hC⟩ := stable_normalized_doubleContact (hK _ (K.corner_mem .C)) hb0 hb5
    (hw _ (K.corner_mem .C)) hu huv hCu hCv
  obtain ⟨dD,hdD,hD⟩ := stable_normalized_doubleContact (hK _ (K.corner_mem .D)) hb0 hb5
    (hw _ (K.corner_mem .D)) hw0 hwz hDw hDz
  have hkC (t : ℝ) (ht : t = D.k ∨ t = D.l) :
      b 0 * doubleContact u v dC t = (b 1*K.lower.a1) * evenProduct D.e D.f R.eL R.fU t :=
    (hC t).symm.trans (K.pairing_at_odd_root_even_lower D R ht .C (Or.inl rfl))
  have hkD (t : ℝ) (ht : t = D.k ∨ t = D.l) :
      b 0 * doubleContact w z dD t = (b 1*K.lower.a1) * evenProduct D.e D.f R.eL R.fU t :=
    (hD t).symm.trans (K.pairing_at_odd_root_even_lower D R ht .D (Or.inr rfl))
  have ha1 : 0 < K.lower.a1 := (quintic_coefficients_pos (hK _ K.lower_mem)).1
  have hscale := ne_of_gt (mul_pos hb1 ha1)
  have hRC := scaled_values_ratio (ne_of_gt hb0) hscale (hkC _ (Or.inl rfl)) (hkC _ (Or.inr rfl))
  have hRD := scaled_values_ratio (ne_of_gt hb0) hscale (hkD _ (Or.inl rfl)) (hkD _ (Or.inr rfl))
  exact cd_contact_impossible ho hdC hdD (hRC.trans hRD.symm) hRC

end
end SPR.N5.Direct
