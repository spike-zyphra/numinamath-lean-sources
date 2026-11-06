import Mathlib

theorem algebra_297817 {α β : ℝ} (h₀ : α^3-3*α^2+5*α-4=0) (h₁ : β^3-3*β^2+5*β-2=0) : α+β=2 := by
  have h2 : β = 2 - α := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 2), sq_nonneg (α - 1), sq_nonneg (β - 1),
      h₀, h₁, sq_nonneg (α - β), sq_nonneg (α + β - 2)]
  linarith [h2]