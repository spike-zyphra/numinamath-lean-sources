import Mathlib

theorem algebra_21130 (r : ℝ) (h₀ : r > 0) (h₁ : (2 * r) ^ 2 = 196) :
    π * r ^ 2 = 49 * π := by
  have h2 : r ^ 2 = 49 := by
    nlinarith 
  calc 
    π * r ^ 2 = π * 49 := by rw [h2]
    _ = 49 * π := by ring