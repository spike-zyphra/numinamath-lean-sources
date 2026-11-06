import Mathlib

theorem inequalities_226285 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) : (2 + a) * (2 + b) ≥ c * d := by
  have h1 : c * d ≤ (c ^ 2 + d ^ 2) / 2 := by
    nlinarith [sq_nonneg (c - d), sq_nonneg (c + d)]
  have h2 : c ^ 2 + d ^ 2 = 4 - a ^ 2 - b ^ 2 := by
    nlinarith 
  have h3 : c * d ≤ (4 - a ^ 2 - b ^ 2) / 2 := by 
    rw [show (4 - a ^ 2 - b ^ 2 : ℝ) / 2 = (c ^ 2 + d ^ 2) / 2 by 
      linarith [h2]] at *
    linarith [h1]
  nlinarith [sq_nonneg (a + b + 2), sq_nonneg (a - b), sq_nonneg (a + b - 2)]