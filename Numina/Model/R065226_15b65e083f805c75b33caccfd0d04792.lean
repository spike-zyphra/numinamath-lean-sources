import Mathlib

theorem algebra_184419 (α β : ℝ) (h₁ : α^3 - 3 * α^2 + 5 * α - 4 = 0) (h₂ : β^3 - 3 * β^2 + 5 * β - 2 = 0) : α + β = 2 := by
  have eq1 : (α - 1) ^ 3 + 2 * (α - 1) - 1 = 0 := by
    nlinarith [h₁]
  have eq2 : (β - 1) ^ 3 + 2 * (β - 1) + 1 = 0 := by
    nlinarith [h₂]
  have h5 : (α - 1) ^ 3 + (β - 1) ^ 3 + 2 * ((α - 1) + (β - 1)) = 0 := by
    nlinarith [eq1, eq2]
  have h6 : ((α - 1) + (β - 1)) * ( ((α - 1) + (β - 1)) ^ 2 + 2 - 3 * ((α - 1) * (β - 1)) ) = 0 := by
    nlinarith [h5]
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where h7 is true
    linarith
  · -- Case where h8 is true
    have h9 : ((α - 1) + (β - 1)) ^ 2 + 2 - 3 * ((α - 1) * (β - 1)) = 0 := by linarith
    nlinarith [sq_nonneg (α - 1 - (β - 1)), sq_nonneg (α - 1 + (β - 1)), sq_nonneg (α - 1 - 1), sq_nonneg (β - 1 - 1), h9, eq1, eq2]