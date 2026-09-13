import SPR.N5.Comparisons.RootRatios

/-!
# Factorized double contacts

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
把两组二重接触分解的公共取值比，与三类根序不等式组合成矛盾。
-/
namespace SPR.N5.Direct
noncomputable section

def doubleContact (r s d t : ℝ) : ℝ := (t + d) * (t - r) ^ 2 * (t - s) ^ 2

def rootPairRatio (x y r s : ℝ) : ℝ := ((x - r) * (x - s)) / ((y - r) * (y - s))

theorem doubleContact_ratio (x y r s d : ℝ) :
    doubleContact r s d x / doubleContact r s d y =
      ((x + d) / (y + d)) * (rootPairRatio x y r s) ^ 2 := by
  unfold doubleContact rootPairRatio
  calc
    _ = ((x + d) * ((x - r) * (x - s)) ^ 2) /
        ((y + d) * ((y - r) * (y - s)) ^ 2) := by congr 1 <;> ring
    _ = _ := by rw [mul_div_mul_comm, ← div_pow]

theorem rootPairRatio_inner (x y r s : ℝ) :
    rootPairRatio x y r s = inner x y r * inner x y s := by
  unfold rootPairRatio inner
  rw [div_mul_div_comm]
  congr 1
  ring

theorem reversed_sub_div (x y r : ℝ) : (x - r) / (y - r) = (r - x) / (r - y) := by
  rw [← neg_sub r x, ← neg_sub r y, neg_div_neg_eq]

theorem rootPairRatio_outer (x y r s : ℝ) :
    rootPairRatio x y r s = outer x y r * outer x y s := by
  unfold rootPairRatio outer
  rw [mul_div_mul_comm, reversed_sub_div x y r, reversed_sub_div x y s]

theorem rootPairRatio_below_outer (x y w z : ℝ) :
    rootPairRatio x y w z = below x y w * outer x y z := by
  unfold rootPairRatio below outer
  rw [mul_div_mul_comm, reversed_sub_div x y z]

/-- Common odd-part product when both odd quadratics are monic. -/
def oddProduct (k ell α β t : ℝ) : ℝ :=
  t * ((t - k) * (t - α)) * ((t - ell) * (t - β))

/-- Common even-part product, apart from its positive leading coefficient. -/
def evenProduct (e f α β t : ℝ) : ℝ :=
  ((t - e) * (t - α)) * ((t - f) * (t - β))

theorem oddProduct_ratio (e f k ell α β : ℝ) :
    oddProduct k ell α β e / oddProduct k ell α β f =
      (e / f) * (inner e f k * inner e f α * (outer e f ell * outer e f β)) := by
  unfold oddProduct
  rw [mul_div_mul_comm, mul_div_mul_comm]
  change (e / f) * rootPairRatio e f k α * rootPairRatio e f ell β = _
  rw [rootPairRatio_inner, rootPairRatio_outer]
  ring

theorem evenProduct_ratio (k ell e f α β : ℝ) :
    evenProduct e f α β k / evenProduct e f α β ell =
      (below k ell e * inner k ell f) * (below k ell α * inner k ell β) := by
  unfold evenProduct
  rw [mul_div_mul_comm]
  change rootPairRatio k ell e α * rootPairRatio k ell f β = _
  rw [rootPairRatio_inner k ell f β]
  unfold rootPairRatio below
  rw [mul_div_mul_comm]
  ring

/-- BC cannot have shared double-contact ratios and the ratio forced by O₊. -/
theorem bc_contact_impossible {e k r α s f u β v ell d₁ d₂ : ℝ}
    (h : 0 < e ∧ e < k ∧ k < r ∧ r < α ∧ α < s ∧ s < f ∧
      f < u ∧ u < β ∧ β < v ∧ v < ell)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hshared : doubleContact r s d₁ e / doubleContact r s d₁ f =
      doubleContact u v d₂ e / doubleContact u v d₂ f)
    (hodd : doubleContact r s d₁ e / doubleContact r s d₁ f =
      oddProduct k ell α β e / oddProduct k ell α β f) : False := by
  have horder := h
  rcases h with ⟨he, hek, hkr, hrα, hαs, hsf, hfu, huβ, hβv, hvell⟩
  have hef : e < f := by linarith
  have hRA : doubleContact r s d₁ e / doubleContact r s d₁ f =
      ((e + d₁) / (f + d₁)) * (inner e f r * inner e f s) ^ 2 := by
    rw [doubleContact_ratio, rootPairRatio_inner]
  have hRB : doubleContact r s d₁ e / doubleContact r s d₁ f =
      ((e + d₂) / (f + d₂)) * (outer e f u * outer e f v) ^ 2 := by
    rw [hshared, doubleContact_ratio, rootPairRatio_outer]
  have hb := shared_contact_ratio_bounds he hef hd₁ hd₂
    (mul_pos (inner_pos (by linarith : e < r) (by linarith : r < f))
      (inner_pos (by linarith : e < s) hsf))
    (mul_pos (outer_pos hef hfu) (outer_pos hef (by linarith : f < v))) hRA hRB
  have hc := bc_root_ratio_lt horder
  rw [oddProduct_ratio] at hodd
  rw [← hodd] at hc
  exact (lt_asymm hb.1 hc)

/-- AD cannot have shared double-contact ratios and the ratio forced by O₋. -/
theorem ad_contact_impossible {w e r α s k f ell z β d₁ d₂ : ℝ}
    (h : 0 < w ∧ w < e ∧ e < r ∧ r < α ∧ α < s ∧ s < k ∧
      k < f ∧ f < ell ∧ ell < z ∧ z < β)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hshared : doubleContact r s d₁ e / doubleContact r s d₁ f =
      doubleContact w z d₂ e / doubleContact w z d₂ f)
    (hodd : doubleContact r s d₁ e / doubleContact r s d₁ f =
      oddProduct k ell α β e / oddProduct k ell α β f) : False := by
  have horder := h
  rcases h with ⟨hw, hwe, her, hrα, hαs, hsk, hkf, hfell, hellz, hzβ⟩
  have he : 0 < e := by linarith
  have hef : e < f := by linarith
  have hRA : doubleContact r s d₁ e / doubleContact r s d₁ f =
      ((e + d₁) / (f + d₁)) * (inner e f r * inner e f s) ^ 2 := by
    rw [doubleContact_ratio, rootPairRatio_inner]
  have hRB : doubleContact r s d₁ e / doubleContact r s d₁ f =
      ((e + d₂) / (f + d₂)) * (below e f w * outer e f z) ^ 2 := by
    rw [hshared, doubleContact_ratio, rootPairRatio_below_outer]
  have hb := shared_contact_ratio_bounds he hef hd₁ hd₂
    (mul_pos (inner_pos her (by linarith : r < f))
      (inner_pos (by linarith : e < s) (by linarith : s < f)))
    (mul_pos (below_pos hwe hef) (outer_pos hef (by linarith : f < z))) hRA hRB
  have hc := ad_root_ratio_gt horder
  rw [oddProduct_ratio] at hodd
  rw [← hodd] at hc
  exact (lt_asymm hb.2 hc)

/-- CD cannot have shared double-contact ratios and the ratio forced by E₋. -/
theorem cd_contact_impossible {α w e k f u β v ell z d₁ d₂ : ℝ}
    (h : 0 < α ∧ α < w ∧ w < e ∧ e < k ∧ k < f ∧ f < u ∧
      u < β ∧ β < v ∧ v < ell ∧ ell < z)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hshared : doubleContact u v d₁ k / doubleContact u v d₁ ell =
      doubleContact w z d₂ k / doubleContact w z d₂ ell)
    (heven : doubleContact u v d₁ k / doubleContact u v d₁ ell =
      evenProduct e f α β k / evenProduct e f α β ell) : False := by
  have horder := h
  rcases h with ⟨hα, hαw, hwe, hek, hkf, hfu, huβ, hβv, hvell, hellz⟩
  have hk : 0 < k := by linarith
  have hkell : k < ell := by linarith
  have hRA : doubleContact u v d₁ k / doubleContact u v d₁ ell =
      ((k + d₁) / (ell + d₁)) * (inner k ell u * inner k ell v) ^ 2 := by
    rw [doubleContact_ratio, rootPairRatio_inner]
  have hRB : doubleContact u v d₁ k / doubleContact u v d₁ ell =
      ((k + d₂) / (ell + d₂)) * (below k ell w * outer k ell z) ^ 2 := by
    rw [hshared, doubleContact_ratio, rootPairRatio_below_outer]
  have hb := shared_contact_ratio_bounds hk hkell hd₁ hd₂
    (mul_pos (inner_pos (by linarith : k < u) (by linarith : u < ell))
      (inner_pos (by linarith : k < v) hvell))
    (mul_pos (below_pos (by linarith : w < k) hkell) (outer_pos hkell hellz)) hRA hRB
  have hc := cd_root_ratio_lt horder
  rw [evenProduct_ratio] at heven
  rw [← heven] at hc
  exact (lt_asymm hb.1 hc)

end
end SPR.N5.Direct
