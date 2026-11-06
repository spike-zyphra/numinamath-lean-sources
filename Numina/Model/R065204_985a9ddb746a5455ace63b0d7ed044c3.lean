import Mathlib

theorem algebra_308718 (x y z : ℝ) (h1 : x^2 - y * z - 8 * x + 7 = 0) (h2 : y^2 + z^2 + y * z - 6 * x + 6 = 0) :
    1 ≤ x ∧ x ≤ 9 := by
  have eq1 : y * z = x^2 - 8 * x + 7 := by
    linarith
  have h3 : y^2 + z^2 = -x^2 + 14 * x - 13 := by
    have h_eq : y^2 + z^2 + y * z = 6 * x - 6 := by
      linarith
    rw [eq1] at h_eq
    nlinarith
  have h4 : y * z ≤ (y^2 + z^2)/2 := by
    linarith [sq_nonneg (y - z)]
  rw [eq1] at h4
  rw [show y^2 + z^2 = -x^2 + 14 * x - 13 by linarith [h3]] at h4
  have h5 : x^2 - 10 * x + 9 ≤ 0 := by
    nlinarith
  constructor
  · -- Show that 1 ≤ x
    nlinarith
  · -- Show that x ≤ 9
    nlinarith