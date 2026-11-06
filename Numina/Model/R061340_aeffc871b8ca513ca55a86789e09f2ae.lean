import Mathlib

theorem algebra_298464 (a b c : ℝ) (h₀ : a + b - 2 * c = -3) (h₁ : a ^ 2 + b ^ 2 + 2 * c ^ 2 + 8 * c = 5) :
    a * b ≥ 25 / 16 := by
  have h2 : a + b = 2 * c - 3 := by linarith 
  have h3 : (a + b) ^ 2 = (2 * c - 3) ^ 2 := by rw [h2]
  have h4 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by ring
  have h5 : a^2 + b^2 + 2 * (a * b) = (2 * c - 3) ^ 2 := by linarith [h3, h4]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - (2 * c - 3)), sq_nonneg (a - b), sq_nonneg (c - 5 / 4), sq_nonneg (a + b - 2 * c + 3)]