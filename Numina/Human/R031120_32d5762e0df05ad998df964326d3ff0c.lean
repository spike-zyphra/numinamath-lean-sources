import Mathlib

/- $x, y, z$ are positive reals such that $x \leq 1$. Prove that
$$xy+y+2z \geq 4 \sqrt{xyz}$$ -/
theorem inequalities_38367 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hle : x ≤ 1) :
    x * y + y + 2 * z ≥ 4 * Real.sqrt (x * y * z) := by
  have h1 := sq_nonneg (x - 1)
  have h2 := sq_nonneg (y - 1)
  have h3 := sq_nonneg (z - 1)
  have h4 := sq_nonneg (Real.sqrt (x * y * z) - 1)
  have h5 := sq_nonneg (Real.sqrt (x * y * z) - x)
  have h6 := sq_nonneg (Real.sqrt (x * y * z) - y)
  have h7 := sq_nonneg (Real.sqrt (x * y * z) - z)
  nlinarith [Real.sq_sqrt (mul_nonneg (mul_nonneg hx.le hy.le) hz.le),
    Real.sq_sqrt (mul_nonneg hx.le hy.le),
    Real.sq_sqrt (mul_nonneg hx.le hz.le),
    Real.sq_sqrt (mul_nonneg hy.le hz.le)]