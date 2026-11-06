import Mathlib

theorem algebra_160633 {x y : ℝ} (h1 : x^2 * y + x * y^2 - 2 * x - 2 * y + 10 = 0)
    (h2 : x^3 * y - x * y^3 - 2 * x^2 + 2 * y^2 - 30 = 0) :
    (x, y) = (-4, -1) := by
  have eq1 : (x * y - 2) * (x + y) = -10 := by
    nlinarith [sq_nonneg (x * y - 2), sq_nonneg (x + y)]
  have eq2 : (x * y - 2) * (x + y) * (x - y) = 30 := by
    nlinarith [sq_nonneg (x * y - 2), sq_nonneg (x + y), sq_nonneg (x - y)]
  have h3 : x - y = -3 := by
    nlinarith [eq1, eq2]
  have h4 : x = y - 3 := by linarith
  rw [h4] at eq1
  have h5 : 2 * y^3 - 9 * y^2 + 5 * y + 16 = 0 := by
    nlinarith
  have h6 : (y + 1) * (2 * y^2 - 11 * y + 16) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- case $y + 1 = 0$, so $y = -1$
    have hy : y = -1 := by linarith
    have hx : x = -4 := by
      linarith [h4, hy]
    simp [hx, hy]
  · -- case $2y^2 - 11y + 16 = 0$, which has no real solutions
    nlinarith [sq_nonneg (y - 11 / 4), sq_nonneg (x + 4)]