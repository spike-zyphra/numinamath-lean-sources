import Mathlib

theorem algebra_312464 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a * b + b * c + c * a = 0)
    (h₂ : a * b * c = 1) :
    |a + b| ≥ 4 * |c| := by
  cases' abs_cases (a + b) with h h <;> 
    cases' abs_cases c with h' h' <;> 
      all_goals
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_nonneg (show 0 ≤ b - a by linarith [h₀.left]) 
          (show 0 ≤ c - b by linarith [h₀.right]), 
          sq_nonneg (a + b + c), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]