import Mathlib

theorem algebra_209767 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x + 1) * (y + 1) = 2 * (x * y)) :
    (x ^ 2 - 1) * (y ^ 2 - 1) = 4 * (x * y) := by 
  have h1 : x + y + 1 = x * y := by
    nlinarith
  have h2 : (x ^ 2 - 1) * (y ^ 2 - 1) = x^2 * y^2 - (x^2 + y^2) + 1 := by
    ring
  have h3 : x^2 + y^2 = (x * y) ^ 2 - 4 * (x * y) + 1 := by 
    nlinarith [h1, sq_nonneg (x - y), sq_nonneg (x + y - (x * y) + 1)]
  rw [h2, h3]
  ring