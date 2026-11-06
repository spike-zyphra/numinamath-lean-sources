import Mathlib

theorem algebra_300846 (x y z : ℝ) (h₀ : x + y + z = 5) (h₁ : x * y + y * z + z * x = 3) :
    z ≤ 13 / 3 ∧ z ≥ -1 := by
  have h2 : x + y = 5 - z := by linarith

  have h3 : x * y = z^2 - 5 * z + 3 := by
    have h4 : x * y + y * z + z * x = 3 := h₁
    have h5 : x * y + z * (x + y) = 3 := by
      linarith [h4]
    rw [h2] at h5
    nlinarith

  have h4 : (x - y) ^ 2 ≥ 0 := by
    apply sq_nonneg

  have h5 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
    ring
    <;> nlinarith

  have h6 : -3 * z^2 + 10 * z + 13 ≥ 0 := by
    rw [h2, h3] at h5
    nlinarith [h5, h4]

  constructor
  · -- Show that z ≤ 13/3
    nlinarith

  · -- Show that z ≥ -1
    nlinarith