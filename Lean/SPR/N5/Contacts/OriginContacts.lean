import SPR.N5.Contacts.OrderedContacts

/-! The origin-zero BC obstruction as an exact polynomial identity contradiction.
## 与论文的对应

论文 §5：接触点重数、符号和极小顶点之间的联系。
在分子常数项为零的边界，证明 B、C 两组接触不能具有指定次序。
-/
namespace SPR.N5.Direct

noncomputable section
open Polynomial

def rootQuadratic (r s : ℝ) : ℝ[X] := (X - C r) * (X - C s)

theorem rootQuadratic_expand (r s : ℝ) :
    rootQuadratic r s = X ^ 2 - C (r + s) * X + C (r * s) := by
  simp only [rootQuadratic, map_add, map_mul]
  ring

theorem rootQuadratic_coeff_one (r s : ℝ) :
    (rootQuadratic r s).coeff 1 = -(r + s) := by
  rw [rootQuadratic_expand]
  norm_num only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C,
    ite_false, ite_true, zero_sub, add_zero]

theorem origin_bc_polynomial_impossible {r s u v c b₁ b₃ d₁ d₃ d₅ : ℝ}
    (hr : 0 < r) (hrs : r < s) (hsu : s < u) (huv : u < v)
    (hc : 0 < c) (hb₁ : 0 < b₁) (hd₁ : 0 ≤ d₁) (hd₃ : 0 < d₃) (hd₅ : 0 ≤ d₅)
    (hpoly : C c * ((rootQuadratic u v) ^ 2 - (rootQuadratic r s) ^ 2) =
      -(C b₁ * X - C b₃) * (C d₁ * X ^ 2 + C d₃ * X + C d₅)) : False := by
  let S : ℝ := u + v - r - s
  let τ : ℝ := (u * v - r * s) / S
  let W : ℝ[X] := rootQuadratic u v + rootQuadratic r s
  let D : ℝ[X] := C d₁ * X ^ 2 + C d₃ * X + C d₅
  have hS : 0 < S := by dsimp [S]; linarith
  have hprod : r * s < u * v :=
    mul_lt_mul (hrs.trans hsu) (hsu.trans huv).le (hr.trans hrs) (hr.trans (hrs.trans hsu)).le
  have hτ : 0 < τ := div_pos (sub_pos.mpr hprod) hS
  have hSτ : S * τ = u * v - r * s := by
    dsimp [τ]
    field_simp
  have hdiff : rootQuadratic u v - rootQuadratic r s = -C S * (X - C τ) := by
    calc
      _ = -C S * X + C (u * v - r * s) := by
        rw [rootQuadratic_expand, rootQuadratic_expand]
        dsimp [S]
        simp only [map_add, map_sub, map_mul]
        ring
      _ = -C S * X + C (S * τ) := by rw [hSτ]
      _ = _ := by rw [map_mul]; ring
  have hDs : 0 < D.eval τ := by
    dsimp [D]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    have := mul_nonneg hd₁ (sq_nonneg τ)
    have := mul_pos hd₃ hτ
    linarith
  have heval := congrArg (fun p : ℝ[X] => p.eval τ) hdiff
  have hvalues : (rootQuadratic u v).eval τ = (rootQuadratic r s).eval τ := by
    simp only [eval_sub, eval_mul, eval_neg, eval_C, eval_X, sub_self, mul_zero] at heval
    exact sub_eq_zero.mp heval
  have heq := congrArg (fun p : ℝ[X] => p.eval τ) hpoly
  have hbτ : b₁ * τ - b₃ = 0 := by
    change C c * ((rootQuadratic u v) ^ 2 - (rootQuadratic r s) ^ 2) =
      -(C b₁ * X - C b₃) * D at hpoly
    change (C c * ((rootQuadratic u v) ^ 2 - (rootQuadratic r s) ^ 2)).eval τ =
      (-(C b₁ * X - C b₃) * D).eval τ at heq
    simp only [eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_neg, hvalues,
      sub_self, mul_zero] at heq
    have hmul : (b₁ * τ - b₃) * D.eval τ = 0 := by nlinarith [heq]
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hDs)
  have hb₃ : b₃ = b₁ * τ := by linarith
  have hfactor : (X - C τ) * (C (c * S) * W) = (X - C τ) * (C b₁ * D) := by
    calc
      _ = -(C c * ((rootQuadratic u v) ^ 2 - (rootQuadratic r s) ^ 2)) := by
        rw [show (rootQuadratic u v) ^ 2 - (rootQuadratic r s) ^ 2 =
          (rootQuadratic u v - rootQuadratic r s) * W by dsimp [W]; ring, hdiff]
        simp only [map_mul]
        ring
      _ = (C b₁ * X - C b₃) * D := by rw [hpoly]; ring
      _ = _ := by rw [hb₃, map_mul]; ring
  have hcancel := mul_left_cancel₀ (monic_X_sub_C τ).ne_zero hfactor
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) hcancel
  dsimp only at hcoeff
  have hDcoeff : D.coeff 1 = d₃ := by
    dsimp [D]
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
      ite_false, ite_true, add_zero, zero_add]
  rw [coeff_C_mul, coeff_C_mul, hDcoeff] at hcoeff
  change c * S * (rootQuadratic u v + rootQuadratic r s).coeff 1 = b₁ * d₃ at hcoeff
  rw [coeff_add, rootQuadratic_coeff_one, rootQuadratic_coeff_one] at hcoeff
  have hsum : 0 < u + v + (r + s) := by linarith
  have hleft : 0 < c * S * (u + v + (r + s)) := mul_pos (mul_pos hc hS) hsum
  have hright : 0 < b₁ * d₃ := mul_pos hb₁ hd₃
  nlinarith only [hcoeff, hleft, hright]

end
end SPR.N5.Direct
