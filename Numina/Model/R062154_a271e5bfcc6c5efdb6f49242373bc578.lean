import Mathlib

theorem inequalities_60924 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 2) :
    x ^ 3 * y ^ 3 * (x ^ 3 + y ^ 3) ≤ 2 := by
  have h1 : y = 2 - x := by linarith
  have h3 : x * y ≤ 1 := by
    nlinarith [sq_nonneg (x - 1), hxy]
  have h2 : x ^ 3 + y ^ 3 = 8 - 6 * (x * y) := by
    rw [h1]
    have h3 : x ^ 3 + (2 - x) ^ 3 = 8 - 6 * (x * (2 - x)) := by
      nlinarith [sq_nonneg (x - 1)]
    linarith [h3]
  have eq1 : x ^ 3 * y ^ 3 = (x * y) ^ 3 := by
    have h1' : y = 2 - x := h1
    rw [h1']
    all_goals nlinarith [sq_nonneg (x - 1)]
  rw [eq1]
  rw [h2]
  nlinarith [sq_nonneg ((x * y) - 1), sq_nonneg ((x * y) * (x * y - 1)), sq_nonneg (x * y), sq_nonneg ((x * y) - 1), mul_pos hx hy, h3]