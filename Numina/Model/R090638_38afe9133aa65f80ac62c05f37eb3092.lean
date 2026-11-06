import Mathlib

theorem algebra_8745 {a b : ℝ} (h : a^2 + a * b + b^2 = 3) :
    a^2 + b^2 - a * b ≤ 9 ∧ a^2 + b^2 - a * b ≥ 1 := by
  -- First part: proving the maximum
  have h1 : a^2 + b^2 - a * b ≤ 9 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  
  -- Second part: proving the minimum
  have h2 : a^2 + b^2 - a * b ≥ 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

  constructor
  · linarith
  
  · linarith