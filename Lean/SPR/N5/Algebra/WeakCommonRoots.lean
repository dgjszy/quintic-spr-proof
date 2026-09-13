import SPR.N5.Preliminaries.InterlacingSigns

/-! Exclude common positive numerator E/O zeros by interval perturbations and
square-factor cancellation, without a half-plane minimum principle.
## 与论文的对应

论文 §4.1–4.2：非负性的代数后果、分子零点及互素性。
利用独立系数扰动与半轴非负性，排除分子偶奇部分的公共正根。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial Filter
open scoped Topology

def numeratorEvenSlope (b : Vec6) (t : ℝ) : ℝ := 2 * b 1 * t - b 3
def numeratorOddSlope (b : Vec6) (t : ℝ) : ℝ := 2 * b 0 * t - b 2

theorem pairing_derivative_eval (a : Poly5) (b : Vec6) (t : ℝ) :
    (pairingPoly a b).derivative.eval t =
      numeratorEvenSlope b t * evenPart a t + numeratorEven b t * (2*a.a1*t-a.a3) +
      numeratorOdd b t * oddPart a t +
      t * (numeratorOddSlope b t * oddPart a t + numeratorOdd b t * (2*t-a.a2)) := by
  simp [pairingPoly, numeratorEvenPoly, numeratorOddPoly, denominatorEvenPoly,
    denominatorOddPoly, numeratorEvenSlope, numeratorOddSlope, numeratorEven,
    numeratorOdd, evenPart, oddPart, derivative_mul]
  ring

theorem Box5.update_a5_mem (K : Box5) {a : Poly5} (ha : K.Contains a) {v : ℝ}
    (hl : K.lower.a5 ≤ v) (hu : v ≤ K.upper.a5) : K.Contains {a with a5 := v} := by
  rcases ha with ⟨h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u,_,_⟩
  exact ⟨h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u,hl,hu⟩

theorem Box5.update_a4_mem (K : Box5) {a : Poly5} (ha : K.Contains a) {v : ℝ}
    (hl : K.lower.a4 ≤ v) (hu : v ≤ K.upper.a4) : K.Contains {a with a4 := v} := by
  rcases ha with ⟨h1l,h1u,h2l,h2u,h3l,h3u,_,_,h5l,h5u⟩
  exact ⟨h1l,h1u,h2l,h2u,h3l,h3u,hl,hu,h5l,h5u⟩

theorem pairing_derivative_a5_difference (a : Poly5) (b : Vec6) (t u l : ℝ) :
    (pairingPoly {a with a5 := u} b).derivative.eval t -
      (pairingPoly {a with a5 := l} b).derivative.eval t =
        (u-l) * numeratorEvenSlope b t := by
  simp only [pairing_derivative_eval, evenPart, oddPart]
  ring

theorem pairing_derivative_a4_difference (a : Poly5) (b : Vec6) (t u l : ℝ) :
    (pairingPoly {a with a4 := u} b).derivative.eval t -
      (pairingPoly {a with a4 := l} b).derivative.eval t =
        (u-l) * (numeratorOdd b t + t * numeratorOddSlope b t) := by
  simp only [pairing_derivative_eval, evenPart, oddPart]
  ring

theorem Box5.common_root_slopes_zero (K : Box5) (hwidth : K.FullWidth) (b : Vec6)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r : ℝ} (hr : 0 < r) (he : numeratorEven b r = 0) (ho : numeratorOdd b r = 0) :
    numeratorEvenSlope b r = 0 ∧ numeratorOddSlope b r = 0 := by
  have hd (a : Poly5) (ha : K.Contains a) : (pairingPoly a b).derivative.eval r = 0 := by
    apply nonnegative_contact_derivative hr
      (by simpa only [pairingPoly_eval] using hw a ha)
    simp [pairingPoly_eval, generalPairing, he, ho]
  have heq := pairing_derivative_a5_difference K.lower b r K.upper.a5 K.lower.a5
  rw [hd _ (K.update_a5_mem K.lower_mem K.h5 le_rfl),
    hd _ (K.update_a5_mem K.lower_mem le_rfl K.h5), sub_self] at heq
  have he' := (mul_eq_zero.mp heq.symm).resolve_left
    (ne_of_gt (sub_pos.mpr hwidth.2.2.2.2))
  have hoq := pairing_derivative_a4_difference K.lower b r K.upper.a4 K.lower.a4
  rw [hd _ (K.update_a4_mem K.lower_mem K.h4 le_rfl),
    hd _ (K.update_a4_mem K.lower_mem le_rfl K.h4), sub_self, ho, zero_add] at hoq
  have hot := (mul_eq_zero.mp hoq.symm).resolve_left
    (ne_of_gt (sub_pos.mpr hwidth.2.2.2.1))
  exact ⟨he', (mul_eq_zero.mp hot).resolve_left (ne_of_gt hr)⟩

theorem quadratic_double_factor (u v w r : ℝ)
    (hval : u*r^2-v*r+w = 0) (hslope : 2*u*r-v = 0) (t : ℝ) :
    u*t^2-v*t+w = u*(t-r)^2 := by
  have hv : v = 2*u*r := by linarith
  have hw : w = u*r^2 := by rw [hv] at hval; nlinarith
  rw [hv, hw]
  ring

theorem cancel_square_nonneg {q : ℝ → ℝ} (hq : Continuous q) (r : ℝ)
    (hw : ∀ t : ℝ, 0 ≤ t → 0 ≤ (t-r)^2 * q t) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ q t := by
  have hoff (t : ℝ) (ht : 0 ≤ t) (hne : t ≠ r) : 0 ≤ q t :=
    (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))).mp (hw t ht)
  intro t ht
  by_cases htr : t = r
  · subst t
    have hl : Tendsto (fun n : ℕ => r + 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := r)).add tendsto_one_div_add_atTop_nhds_zero_nat
    apply ge_of_tendsto ((hq.tendsto r).comp hl)
    apply Eventually.of_forall
    intro n
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact hoff _ (by linarith) (by linarith)
  · exact hoff t ht htr

/-- Full independent widths prevent a common positive E/O zero. The proof
reduces a hypothetical common double factor to a forbidden linear weak numerator. -/
theorem Box5.no_common_positive_numerator_root (K : Box5) (hK : K.RobustlyHurwitz)
    (hwidth : K.FullWidth) {b : Vec6} (hb : b ≠ 0)
    (hw : ∀ a : Poly5, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 ≤ generalPairing a b t)
    {r : ℝ} (hr : 0 < r) (he : numeratorEven b r = 0) (ho : numeratorOdd b r = 0) : False := by
  obtain ⟨he', ho'⟩ := K.common_root_slopes_zero hwidth b hw hr he ho
  have hE (t : ℝ) : numeratorEven b t = b 1 * (t-r)^2 :=
    quadratic_double_factor (b 1) (b 3) (b 5) r he he' t
  have hO (t : ℝ) : numeratorOdd b t = b 0 * (t-r)^2 :=
    quadratic_double_factor (b 0) (b 2) (b 4) r ho ho' t
  have hsq (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ (t-r)^2 * (b 1 * evenPart K.lower t + t * b 0 * oddPart K.lower t) := by
    have h := hw K.lower K.lower_mem t ht
    rw [generalPairing, hE, hO] at h
    convert h using 1 <;> ring
  have hlin := cancel_square_nonneg
    (by unfold evenPart oddPart; fun_prop : Continuous
      (fun t => b 1 * evenPart K.lower t + t * b 0 * oddPart K.lower t)) r hsq
  obtain ⟨hb1, hb0⟩ := linear_weak_pairing_zero (hK K.lower K.lower_mem) (b 1) (b 0) hlin
  have hb3 : b 3 = 0 := by simpa [numeratorEvenSlope, hb1] using he'
  have hb2 : b 2 = 0 := by simpa [numeratorOddSlope, hb0] using ho'
  have hb5 : b 5 = 0 := by simpa [numeratorEven, hb1, hb3] using he
  have hb4 : b 4 = 0 := by simpa [numeratorOdd, hb0, hb2] using ho
  apply hb
  funext i
  fin_cases i <;> simp [hb0, hb1, hb2, hb3, hb4, hb5]

end
end SPR.N5.Direct
