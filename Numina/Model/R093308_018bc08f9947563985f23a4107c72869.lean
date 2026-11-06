import Mathlib

theorem algebra_603919 {α β : ℝ} (h₁ : α^3 - 3 * α^2 + 5 * α = 1) (h₂ : β^3 - 3 * β^2 + 5 * β = 5) : α + β = 2 := by
  have h3 : α^3 - 3 * α^2 + 5 * α - 1 = 0 := by linarith
  have h4 : β^3 - 3 * β^2 + 5 * β - 5 = 0 := by linarith

  have h5 : (α + β - 2) * ( (α - β)^2 + (α + β - 2)^2 + 1 ) = 0 := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (α - (2 - β)), sq_nonneg (α^2 - 2 * α), sq_nonneg (β^2 - 2 * β), 
          sq_nonneg (α + β - 2), sq_nonneg (α - 1), sq_nonneg (β - 1), sq_nonneg (α - β)]

  cases' (mul_eq_zero.1 h5) with h6 h7

  · -- Case where α + β - 2 = 0, i.e., α + β = 2
    linarith

  · -- Case where the second factor is zero
    nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 2)]