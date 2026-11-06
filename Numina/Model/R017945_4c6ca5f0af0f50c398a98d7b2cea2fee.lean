import Mathlib

theorem inequalities_193061
    (a b : ℝ)
    (h₀ : a^3 - b^3 = 2)
    (h₁ : a^5 - b^5 ≥ 4) :
    a^2 + b^2 ≥ 2 := by
  by_contra h 
  push_neg at h 
  have h2 : a^3 - b^3 = 2 := h₀
  have h3 : a^5 - b^5 ≥ 4 := h₁
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg ((a - b) * (a + b)), 
    sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a + 1), sq_nonneg (b - 1), 
    sq_nonneg (a^3 - b^3 - 2), 
    sq_nonneg (a^5 - b^5 - 4), 
    sq_nonneg ((a^2 + b^2) - 2), 
    pow_two_nonneg (a - b), pow_two_nonneg (a + b), 
    mul_nonneg (show 0 ≤ (a - b) ^ 2 by positivity) (show 0 ≤ (a + b) ^ 2 by positivity), 
    pow_two_nonneg ((a - b) * (a + b)), 
    sq_nonneg (a^2 - b^2), 
    sq_nonneg ((a - b) * (a^2 + a * b + b^2))
  ]