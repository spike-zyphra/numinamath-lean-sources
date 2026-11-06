import Mathlib

theorem algebra_12058 (a b : ℝ) (h₀ : a + b - 2 ≥ 0) (h₁ : b - a - 1 ≤ 0) (h₂ : a ≤ 1) :
    (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
  have h3 : 2 * a + b > 0 := by linarith
  have h4 : a + 2 * b ≤ 7 / 5 * (2 * a + b) := by
    linarith
  apply (div_le_iff₀ (by linarith : 2 * a + b > 0)).mpr
  linarith