import Mathlib

theorem inequalities_84282 (x y : ℝ) (h : (x + 1) * (y + 2) = 8) :
    (x * y - 10) ^ 2 ≥ 64 := by
  have h1 : x * y + 2 * x + y = 6 := by
    have h2 : (x + 1) * (y + 2) = 8 := h
    linarith
  have h2 : x * y = 6 - 2 * x - y := by
    linarith
  have h3 : x * y - 10 = -4 - 2 * x - y := by
    linarith [h2]
  rw [h3]
  nlinarith [sq_nonneg (2 * (x + 1) - (y + 2)),
          sq_nonneg (2 * x + y - 4),
          sq_nonneg (2 * x + y - 12),
          sq_nonneg ((x + 1) - 2 * (y + 2)), sq_nonneg ((x + 1) - 2), sq_nonneg ((y + 2) - 4)]