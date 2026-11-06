import Mathlib

theorem algebra_224781 {α β : ℝ} (h₁ : α^3 - 3 * α^2 + 5 * α - 17 = 0) (h₂ : β^3 - 3 * β^2 + 5 * β + 11 = 0) :
    α + β = 2 := by
  nlinarith [sq_nonneg (α - β - 2), sq_nonneg (α + β - 2), sq_nonneg (α - 2), sq_nonneg (β - 2), sq_nonneg (α - β), sq_nonneg (α + β - 2)]