import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307168 :
  IsLeast {x | ∃ a b : ℝ, a ≥ 1 / 2 ∧ b ≥ 1 / 2 ∧ x = a^3 + b^3 + a^2 * b + a * b^2 - 3 * (a^2 + b^2 + a * b) + 3 * (a + b)} 1 := by
  constructor
  · -- First part: Show 1 is in the set
    use 1, 1
    norm_num
  · -- Second part: Show all elements in the set are >= 1
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
      mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ b - 1 / 2 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ a + b - 1 by linarith) (show (0 : ℝ) ≤ a + b - 1 by linarith)
    ]