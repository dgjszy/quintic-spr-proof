import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Definitions used by the quintic SPR proof

Only Hurwitz stability and the real monic quintic coefficient type are defined
here. Frequency positivity, interval membership and the target theorem are
specified in `SPR.N5.Definitions.Frequency`.

## 与论文的对应

论文 §1–2：基本对象、精确主命题与虚轴分解。
定义 Hurwitz 稳定性与首一五次多项式的系数类型；完整主命题见 Frequency。
-/

namespace SPR

open Polynomial

/-- Every complex root of a real polynomial has strictly negative real part. -/
def IsHurwitz (a : ℝ[X]) : Prop :=
  ∀ z : ℂ, (a.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0

end SPR

namespace SPR.N5

/-- Coefficients of the real monic quintic s⁵ + a₁s⁴ + a₂s³ + a₃s² + a₄s + a₅. -/
structure Poly5 where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  a5 : ℝ

namespace Poly5

/-- The polynomial represented by the five coefficients. -/
noncomputable def toPoly (p : Poly5) : Polynomial ℝ :=
  Polynomial.X ^ 5 + Polynomial.C p.a1 * Polynomial.X ^ 4 +
  Polynomial.C p.a2 * Polynomial.X ^ 3 + Polynomial.C p.a3 * Polynomial.X ^ 2 +
  Polynomial.C p.a4 * Polynomial.X + Polynomial.C p.a5

end Poly5
end SPR.N5
