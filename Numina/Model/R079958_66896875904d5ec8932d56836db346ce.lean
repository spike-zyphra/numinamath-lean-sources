import Mathlib

theorem algebra_309172 (x y z : ℝ) (h1 : x + y + z = 5) (h2 : x * y + y * z + z * x = 3) :
    z ≤ 13 / 3 ∧ z ≥ -1 := by
  have h3 : x + y = 5 - z := by linarith
  have h4 : x * y = 3 - 5 * z + z ^ 2 := by
    have h5 : x * y + z * (x + y) = 3 := by
      nlinarith
    rw [h3] at h5
    nlinarith [h5]

  have h6 : (5 - z) ^ 2 - 4 * (3 - 5 * z + z ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - (5 - z)), sq_nonneg (x * y - (3 - 5 * z + z ^ 2))]

  have h7 : -3 * z ^ 2 + 10 * z + 13 ≥ 0 := by
    nlinarith [h6]

  constructor
  · -- Show that z ≤ 13/3
    nlinarith [sq_nonneg (z - 13/3), sq_nonneg (z + 1)]
  · -- Show that z ≥ -1
    nlinarith [sq_nonneg (z - 13/3), sq_nonneg (z + 1)]