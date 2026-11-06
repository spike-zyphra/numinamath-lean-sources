import Mathlib

theorem inequalities_305043 (x1 x2 k : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hsum : x1 + x2 = k) : x1 * x2 ≤ k ^ 2 / 4 := by
  have h1 : x2 = k - x1 := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x1 - k / 2)]