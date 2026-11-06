import Mathlib

theorem algebra_145433 {x y : ℝ} (h1 : x^2 * y + x * y^2 - 2 * x - 2 * y + 10 = 0)
    (h2 : x^3 * y - x * y^3 - 2 * x^2 + 2 * y^2 - 30 = 0) :
    (x, y) = (-4, -1) := by
  have eq1 : (x * y - 2) * (x + y) + 10 = 0 := by
    nlinarith
  have eq2 : (x - y) * (x + y) * (x * y - 2) - 30 = 0 := by
    nlinarith
  have h3 : (x * y - 2) * (x + y) = -10 := by linarith
  have h4 : (x - y) * (x + y) * (x * y - 2) = 30 := by linarith
  have h5 : x - y = -3 := by
    have h6 : (x - y) * (x + y) * (x * y - 2) = (x - y) * ((x * y - 2) * (x + y)) := by ring
    rw [h6] at h4
    rw [show (x * y - 2) * (x + y) = -10 by linarith] at h4
    nlinarith
  have h6 : x = y - 3 := by linarith
  have h7 : y = -1 := by
    rw [h6] at h1
    nlinarith [sq_nonneg (y * (y + 1)), sq_nonneg ((y - 4) * (y + 1)), sq_nonneg (y + 1), sq_nonneg (y ^ 2 + 1), sq_nonneg ((y * 2) + 1), sq_nonneg ((y * 2) - 1)]
  have h8 : x = -4 := by
    linarith [h6, h7]
  simp [h8, h7]
  <;> tauto