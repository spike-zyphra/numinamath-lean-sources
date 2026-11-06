import Mathlib
/- (a) Write 1 as a sum of 4 distinct unit fractions. -/
theorem number_theory_608455 : ∃ a b c d : ℕ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a < b ∧ b < c ∧ c < d ∧ (↑a : ℝ)⁻¹ + (↑b : ℝ)⁻¹ + (↑c : ℝ)⁻¹ + (↑d : ℝ)⁻¹ = 1:= by
  -- We use the values 2, 3, 7, and 42 as our four distinct natural numbers
  use 2, 3, 7, 42
  -- Simplify the goal
  simp
  -- Perform numerical calculations to verify that 1/2 + 1/3 + 1/7 + 1/42 = 1
  norm_num
