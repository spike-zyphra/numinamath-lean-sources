import Mathlib

theorem algebra_145210 {α β : ℝ} (h₀ : α^3-3*α^2+5*α-4=0) (h₁ : β^3-3*β^2+5*β-2=0) : α+β=2 := by
  -- we need to prove α + β = 2.
  have h2 : β = 2 - α := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 2), sq_nonneg (α - 1), sq_nonneg (β - 1)]
  -- from h2, we have that β = 2 - α, therefore α + β = α + (2 - α) = 2
  have h3 : α + β = 2 := by
    linarith [h2]
  exact h3
  all_goals nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 2), sq_nonneg (α - 1), sq_nonneg (β - 1)]