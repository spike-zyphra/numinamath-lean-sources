import Mathlib

theorem inequalities_125994 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 2) :
    x^3 * y^3 * (x^3 + y^3) ≤ 2 := by
  have h1 : y = 2 - x := by linarith
  rw [h1]
  have h2 : 0 < 2 - x := by
    nlinarith [h1, hx, hy]
  have h3 : x * (2 - x) ≤ 1 := by
    nlinarith [sq_nonneg (x - 1)]
  nlinarith [sq_nonneg (x * (2 - x) - 1), sq_nonneg (x - 1), sq_nonneg ((2 - x) - 1),
    sq_nonneg (x ^ 3 - (2 - x) ^ 3), sq_nonneg (x * (2 - x) - 1), 
    mul_pos hx (show 0 < (2 - x) by nlinarith), 
    sq_nonneg ((x + (2 - x) - 2)), 
    sq_nonneg ((x * (2 - x)) ^ 2 - 1), 
    sq_nonneg (x ^ 2 - (2 - x) ^ 2)
  ]