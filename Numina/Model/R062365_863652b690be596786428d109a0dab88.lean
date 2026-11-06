import Mathlib

theorem algebra_307864 {α β : ℝ} (h₁ : α^3-3*α^2+5*α=1) (h₂ : β^3-3*β^2+5*β=5) : α+β=2 := by
  have h3 : α^3 - 3 * α^2 + 5 * α - 1 = 0 := by linarith
  have h4 : β^3 - 3 * β^2 + 5 * β - 5 = 0 := by linarith
  have h5 : β = 2 - α := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 2), sq_nonneg (α - 1), sq_nonneg (β - 1),
      sq_nonneg (α - β), sq_nonneg (α + β - 2)]
  linarith [h5]