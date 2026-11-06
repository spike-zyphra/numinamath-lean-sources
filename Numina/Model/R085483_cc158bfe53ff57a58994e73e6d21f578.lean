import Mathlib

/- If positive real numbers $x$, $y$ satisfy $x\left( x+2y \right)=9$, then the maximum value of ${{x}^{5}}y$ is ___          ___. -/
theorem algebra_10408 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * (x + 2 * y) = 9) : x ^ 5 * y ≤ 54 := by
  have h1 : x ^ 5 * y = (9 - x ^ 2) / 2 * x ^ 4 := by
    have h2 : y = (9 - x ^ 2) / (2 * x) := by
      field_simp [(show 0 < x from hx)]
      nlinarith
    rw [h2]
    field_simp [(show 0 < x from hx)]
    <;> ring_nf <;> nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 6)]
  have h3 : (9 - x ^ 2) / 2 * x ^ 4 ≤ 54 := by
    nlinarith [sq_nonneg (x ^ 2 - 6), sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 4 - 6 * x ^ 2),
      sq_nonneg (x ^ 2), mul_pos (show (0 : ℝ) < x from hx) (show (0 : ℝ) < x from hx),
      sq_nonneg (x ^ 2 - 12 * y), sq_nonneg (x * y - 3 / 2)]
  linarith [h1, h3]