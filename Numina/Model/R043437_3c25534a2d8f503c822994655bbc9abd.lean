import Mathlib

theorem algebra_303018 {α β p : ℝ} (h₁ : α^2 + (p - 2) * α + 1 = 0) (h₂ : β^2 + (p - 2) * β + 1 = 0)
    (h₃ : (1 + α * (p + α) - β) * (1 + β * (p + β) - α) = -7 / 2) :
    p = -1 / 2 ∨ p = 9 / 2 := by

  have eq1 : α^2 = - (p - 2) * α - 1 := by linarith [h₁]
  have eq2 : β^2 = - (p - 2) * β - 1 := by linarith [h₂]
  have eq3 : 1 + α * (p + α) - β = 2 * α - β := by 
    nlinarith [eq1, h₁]
  have eq4 : 1 + β * (p + β) - α = 2 * β - α := by
    nlinarith [eq2, h₂]
  rw [eq3, eq4] at h₃
  have h9 : 4 * p^2 - 16 * p - 9 = 0 := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 4), sq_nonneg (α * β - 1), sq_nonneg (α - β), sq_nonneg (α + β - 4), sq_nonneg (α * β - 1)]
  have h8 : (p - 9 / 2) * (p + 1 / 2) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h8) with h9 h10
  · -- Case where $p - 9/2 = 0$
    right
    linarith
  · -- Case where $p + 1/2 = 0$
    left
    linarith