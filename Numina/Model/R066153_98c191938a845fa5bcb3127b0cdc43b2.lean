import Mathlib

theorem algebra_127455 {x y z : ℝ} (h1 : (x - 1) * (y - 1) * (z - 1) = x * y * z - 1)
    (h2 : (x - 2) * (y - 2) * (z - 2) = x * y * z - 2) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  have eq1 : x * y + x * z + y * z - x - y - z = 0 := by
    nlinarith
  have eq2 : (x + y + z) = 3 := by
    nlinarith [h2, eq1]
  have h3 : x^2 + y^2 + z^2 = 3 := by
    have h4 : (x + y + z)^2 = x^2 + y^2 + z^2 + 2 * (x * y + x * z + y * z) := by ring
    rw [eq2] at h4
    nlinarith [eq1]
  have eq3 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
    nlinarith [h3, eq2]
  have hx : x - 1 = 0 := by
    nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hy : y - 1 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 1)]
  have hz : z - 1 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
  constructor
  · linarith
  constructor
  · linarith
  · linarith