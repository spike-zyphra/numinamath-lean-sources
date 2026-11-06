import Mathlib
theorem algebra_305870 (a b : ℝ) (h : a^2 + a * b + b^2 = 1) :
    1 / 3 ≤ a^2 - a * b + b^2 ∧ a^2 - a * b + b^2 ≤ 3 := by 
  -- First express a ^ 2 - a * b + b ^ 2 in a simlified form by linarith tactic.
  have h1 : a^2 - a * b + b^2 = 1 - 2 * (a * b) := by
    linarith [h]
  constructor
  -- Proving 1/3 ≤ a^2 - a * b + b^2
  · have h2 : 1 / 3 ≤ a^2 - a * b + b^2 := by 
      linarith [sq_nonneg (a - b), sq_nonneg (a + b), h]
    exact h2
  -- Proving a^2 - a * b + b^2 ≤ 3
  · have h3 : a^2 - a * b + b^2 ≤ 3 := by 
      linarith [sq_nonneg (a - b), sq_nonneg (a + b), h]
    exact h3