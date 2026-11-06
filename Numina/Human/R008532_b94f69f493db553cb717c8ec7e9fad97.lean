import Mathlib

/- Positive real numbers $r,s$ satisfy the equations $r^2 + s^2 = 1$ and $r^4 + s^4= \frac{7}{8}$.  Find $rs$. -/
theorem algebra_12858 {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h1 : r^2 + s^2 = 1) (h2 : r^4 + s^4 = 7 / 8) :
    r * s = 1 / 4 := by
  have h3 : 0 < r * s := by nlinarith
  nlinarith [sq_nonneg (r^2 - s^2)]