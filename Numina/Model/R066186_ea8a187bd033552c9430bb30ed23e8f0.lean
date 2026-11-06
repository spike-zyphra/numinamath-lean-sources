import Mathlib

theorem algebra_166038 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d - 2100 = 600 / v) (h₃ : d - 600 = 10.05 / v) :
    d / v = 11.5 := by

  have eq1 : v * d - 2100 * v = 600 := by
    field_simp [(show v ≠ 0 by linarith)] at h₂ ⊢
    linarith

  have eq2 : v * d - 600 * v = (10.05 : ℝ) := by
    field_simp [(show v ≠ 0 by linarith)] at h₃ ⊢
    linarith
  
  have eq3 : -1500 * v = (589.95 : ℝ) := by
    linarith

  have h4 : v < 0 := by
    nlinarith

  linarith