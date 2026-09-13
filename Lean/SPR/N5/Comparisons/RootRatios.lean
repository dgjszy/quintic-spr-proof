import Mathlib

/-!
# Ordered-root ratios

论文 §6：公共取值比、三类严格根序与最终五种排列的排除。
先证明根因子的单调性与公共比值夹逼，再给出 B/C、A/D、C/D 三类不等式。
-/

namespace SPR.N5.Direct

noncomputable section

/-- Root factor for a root strictly between the two evaluation points. -/
def inner (x y z : ℝ) : ℝ := (z - x) / (y - z)
/-- Root factor for a root above the two evaluation points. -/
def outer (x y z : ℝ) : ℝ := (z - x) / (z - y)
/-- Root factor for a root below the two evaluation points. -/
def below (x y z : ℝ) : ℝ := (x - z) / (y - z)

theorem inner_pos {x y z : ℝ} (hx : x < z) (hy : z < y) :
    0 < inner x y z := div_pos (sub_pos.mpr hx) (sub_pos.mpr hy)

theorem outer_pos {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    0 < outer x y z := div_pos (sub_pos.mpr (lt_trans hxy hyz)) (sub_pos.mpr hyz)

theorem below_pos {x y z : ℝ} (hzx : z < x) (hxy : x < y) :
    0 < below x y z := div_pos (sub_pos.mpr hzx) (sub_pos.mpr (lt_trans hzx hxy))

theorem inner_strictMono {x y z w : ℝ}
    (hxy : x < y) (hzy : z < y) (hwy : w < y) (hzw : z < w) :
    inner x y z < inner x y w := by
  apply (div_lt_div_iff₀ (sub_pos.mpr hzy) (sub_pos.mpr hwy)).mpr
  nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hzw)]

theorem outer_strictAnti {x y z w : ℝ}
    (hxy : x < y) (hyz : y < z) (hyw : y < w) (hzw : z < w) :
    outer x y w < outer x y z := by
  apply (div_lt_div_iff₀ (sub_pos.mpr hyw) (sub_pos.mpr hyz)).mpr
  nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hzw)]

theorem below_strictAnti {x y z w : ℝ}
    (hxy : x < y) (hzy : z < y) (hwy : w < y) (hzw : z < w) :
    below x y w < below x y z := by
  apply (div_lt_div_iff₀ (sub_pos.mpr hwy) (sub_pos.mpr hzy)).mpr
  nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hzw)]

theorem one_lt_outer {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    1 < outer x y z := by
  apply (lt_div_iff₀ (sub_pos.mpr hyz)).mpr
  linarith

/-- The positive linear remainder in a double-contact factorization. -/
theorem shifted_ratio_bounds {x y d : ℝ} (hx : 0 < x) (hxy : x < y)
    (hd : 0 < d) : x / y < (x + d) / (y + d) ∧ (x + d) / (y + d) < 1 := by
  have hy : 0 < y := lt_trans hx hxy
  constructor
  · apply (div_lt_div_iff₀ hy (by positivity)).mpr
    nlinarith [mul_pos hd (sub_pos.mpr hxy)]
  · apply (div_lt_iff₀ (by positivity : 0 < y + d)).mpr
    linarith

/-- Two shared squared-factor ratios lie between the geometric product bounds.
No square roots or sampling are used in this proof. -/
theorem shared_squared_ratio_bounds {l X Y A B R : ℝ}
    (hl : 0 < l) (hA : 0 < A) (hB : 0 < B)
    (hX : l < X ∧ X < 1) (hY : l < Y ∧ Y < 1)
    (hRA : R = X * A ^ 2) (hRB : R = Y * B ^ 2) :
    l * (A * B) < R ∧ R < A * B := by
  have hla : l * A ^ 2 < R := by
    rw [hRA]
    exact mul_lt_mul_of_pos_right hX.1 (sq_pos_of_pos hA)
  have hlb : l * B ^ 2 < R := by
    rw [hRB]
    exact mul_lt_mul_of_pos_right hY.1 (sq_pos_of_pos hB)
  have hra : R < A ^ 2 := by
    rw [hRA]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hX.2 (sq_pos_of_pos hA)
  have hrb : R < B ^ 2 := by
    rw [hRB]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hY.2 (sq_pos_of_pos hB)
  rcases le_total A B with hab | hba
  · have ha : A ^ 2 ≤ A * B := by nlinarith only [mul_nonneg hA.le (sub_nonneg.mpr hab)]
    have hb : A * B ≤ B ^ 2 := by nlinarith only [mul_nonneg hB.le (sub_nonneg.mpr hab)]
    exact ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_left hb hl.le) hlb, lt_of_lt_of_le hra ha⟩
  · have hb : B ^ 2 ≤ A * B := by nlinarith only [mul_nonneg hB.le (sub_nonneg.mpr hba)]
    have ha : A * B ≤ A ^ 2 := by nlinarith only [mul_nonneg hA.le (sub_nonneg.mpr hba)]
    exact ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_left ha hl.le) hla, lt_of_lt_of_le hrb hb⟩

theorem shared_contact_ratio_bounds {x y d₁ d₂ A B R : ℝ}
    (hx : 0 < x) (hxy : x < y) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hA : 0 < A) (hB : 0 < B)
    (hRA : R = ((x + d₁) / (y + d₁)) * A ^ 2)
    (hRB : R = ((x + d₂) / (y + d₂)) * B ^ 2) :
    (x / y) * (A * B) < R ∧ R < A * B := by
  exact shared_squared_ratio_bounds (div_pos hx (lt_trans hx hxy)) hA hB
    (shifted_ratio_bounds hx hxy hd₁) (shifted_ratio_bounds hx hxy hd₂) hRA hRB


/-- BC: the ratio forced by the common odd part is too small. -/
theorem bc_root_ratio_lt {e k r α s f u β v ell : ℝ}
    (h : 0 < e ∧ e < k ∧ k < r ∧ r < α ∧ α < s ∧ s < f ∧
      f < u ∧ u < β ∧ β < v ∧ v < ell) :
    (e / f) * (inner e f k * inner e f α * (outer e f ell * outer e f β)) <
      (e / f) * ((inner e f r * inner e f s) * (outer e f u * outer e f v)) := by
  rcases h with ⟨he, hek, hkr, hrα, hαs, hsf, hfu, huβ, hβv, hvell⟩
  have hef : e < f := by linarith
  have hi₁ : inner e f k < inner e f r :=
    inner_strictMono hef (by linarith) (by linarith) hkr
  have hi₂ : inner e f α < inner e f s :=
    inner_strictMono hef (by linarith) hsf hαs
  have hi := mul_lt_mul hi₁ hi₂.le
    (inner_pos (by linarith : e < α) (by linarith : α < f))
    (inner_pos (by linarith : e < r) (by linarith : r < f)).le
  have ho₁ : outer e f ell < outer e f v :=
    outer_strictAnti hef (by linarith) (by linarith) hvell
  have ho₂ : outer e f β < outer e f u :=
    outer_strictAnti hef hfu (by linarith) huβ
  have ho : outer e f ell * outer e f β < outer e f u * outer e f v := by
    have hh := mul_lt_mul ho₂ ho₁.le
      (outer_pos hef (by linarith : f < ell)) (outer_pos hef hfu).le
    simpa only [mul_comm] using hh
  apply mul_lt_mul_of_pos_left _ (div_pos he (by linarith))
  exact mul_lt_mul hi ho.le
    (mul_pos (outer_pos hef (by linarith)) (outer_pos hef (by linarith)))
    (mul_pos (inner_pos (by linarith) (by linarith))
      (inner_pos (by linarith) hsf)).le


/-- AD: the common-odd-part ratio exceeds the contact-product upper bound. -/
theorem ad_root_ratio_gt {w e r α s k f ell z β : ℝ}
    (h : 0 < w ∧ w < e ∧ e < r ∧ r < α ∧ α < s ∧ s < k ∧
      k < f ∧ f < ell ∧ ell < z ∧ z < β) :
    (inner e f r * inner e f s) * (below e f w * outer e f z) <
      (e / f) * (inner e f k * inner e f α * (outer e f ell * outer e f β)) := by
  rcases h with ⟨hw, hwe, her, hrα, hαs, hsk, hkf, hfell, hellz, hzβ⟩
  have he : 0 < e := by linarith
  have hef : e < f := by linarith
  have hi₁ : inner e f s < inner e f k :=
    inner_strictMono hef (by linarith) hkf hsk
  have hi₂ : inner e f r < inner e f α :=
    inner_strictMono hef (by linarith) (by linarith) hrα
  have hi : inner e f r * inner e f s < inner e f k * inner e f α := by
    have hh := mul_lt_mul hi₁ hi₂.le
      (inner_pos her (by linarith : r < f))
      (inner_pos (by linarith : e < k) hkf).le
    simpa only [mul_comm] using hh
  have ho₁ : outer e f z < outer e f ell :=
    outer_strictAnti hef hfell (by linarith) hellz
  have ho₂ : 1 < outer e f β := one_lt_outer hef (by linarith)
  have ho : outer e f z < outer e f ell * outer e f β := by
    have hh := mul_lt_mul ho₁ ho₂.le zero_lt_one (outer_pos hef hfell).le
    simpa only [mul_one] using hh
  have hprod := mul_lt_mul hi ho.le (outer_pos hef (by linarith : f < z))
    (mul_pos (inner_pos (by linarith : e < k) hkf)
      (inner_pos (by linarith : e < α) (by linarith : α < f))).le
  have hlow : below e f w < e / f := by
    apply (div_lt_div_iff₀ (by linarith : 0 < f - w) (by linarith : 0 < f)).mpr
    nlinarith only [mul_pos hw (sub_pos.mpr hef)]
  have hpos : 0 < (inner e f r * inner e f s) * outer e f z :=
    mul_pos (mul_pos (inner_pos her (by linarith))
      (inner_pos (by linarith) (by linarith))) (outer_pos hef (by linarith))
  have hleft := mul_lt_mul_of_pos_right hlow hpos
  have hright := mul_lt_mul_of_pos_left hprod (div_pos he (by linarith : 0 < f))
  calc
    (inner e f r * inner e f s) * (below e f w * outer e f z) =
        below e f w * ((inner e f r * inner e f s) * outer e f z) := by ring
    _ < (e / f) * ((inner e f r * inner e f s) * outer e f z) := hleft
    _ < _ := hright

/-- CD: at the odd-part roots, the common-even-part ratio is too small. -/
theorem cd_root_ratio_lt {α w e k f u β v ell z : ℝ}
    (h : 0 < α ∧ α < w ∧ w < e ∧ e < k ∧ k < f ∧ f < u ∧
      u < β ∧ β < v ∧ v < ell ∧ ell < z) :
    (below k ell e * inner k ell f) * (below k ell α * inner k ell β) <
      (k / ell) * ((inner k ell u * inner k ell v) * (below k ell w * outer k ell z)) := by
  rcases h with ⟨hα, hαw, hwe, hek, hkf, hfu, huβ, hβv, hvell, hellz⟩
  have hk : 0 < k := by linarith
  have hkell : k < ell := by linarith
  have hi₁ : inner k ell f < inner k ell u :=
    inner_strictMono hkell (by linarith) (by linarith) hfu
  have hi₂ : inner k ell β < inner k ell v :=
    inner_strictMono hkell (by linarith) hvell hβv
  have hi := mul_lt_mul hi₁ hi₂.le
    (inner_pos (by linarith : k < β) (by linarith : β < ell))
    (inner_pos (by linarith : k < u) (by linarith : u < ell)).le
  have hb₁ : below k ell e < below k ell w :=
    below_strictAnti hkell (by linarith) (by linarith) hwe
  have hb₂ : below k ell α < k / ell := by
    have hh := below_strictAnti hkell (by linarith : 0 < ell)
      (by linarith : α < ell) hα
    simpa only [below, sub_zero] using hh
  have hb := mul_lt_mul hb₁ hb₂.le
    (below_pos (by linarith : α < k) hkell)
    (below_pos (by linarith : w < k) hkell).le
  have hprod := mul_lt_mul hi hb.le
    (mul_pos (below_pos hek hkell) (below_pos (by linarith : α < k) hkell))
    (mul_pos (inner_pos (by linarith : k < u) (by linarith : u < ell))
      (inner_pos (by linarith : k < v) hvell)).le
  have ho : 1 < outer k ell z := one_lt_outer hkell hellz
  have hpos : 0 < (k / ell) * ((inner k ell u * inner k ell v) * below k ell w) :=
    mul_pos (div_pos hk (by linarith))
      (mul_pos (mul_pos (inner_pos (by linarith) (by linarith))
        (inner_pos (by linarith) hvell)) (below_pos (by linarith) hkell))
  calc
    (below k ell e * inner k ell f) * (below k ell α * inner k ell β) =
        (inner k ell f * inner k ell β) * (below k ell e * below k ell α) := by ring
    _ < (inner k ell u * inner k ell v) * (below k ell w * (k / ell)) := hprod
    _ = (k / ell) * ((inner k ell u * inner k ell v) * below k ell w) := by ring
    _ < ((k / ell) * ((inner k ell u * inner k ell v) * below k ell w)) * outer k ell z := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left ho hpos
    _ = _ := by ring

end
end SPR.N5.Direct
