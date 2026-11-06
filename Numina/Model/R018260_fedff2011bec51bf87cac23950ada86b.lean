import Mathlib

theorem algebra_6954 {c : ℝ} (hc : c > 0) (α : ℝ) (h : α ^ 4 - α ^ 3 + α ^ 2 - (c + 1) * α - (c ^ 2 + c) = 0) : c = α ^ 2 - α := by
  have h1 : (α^2 - α - c) * (α^2 + (c + 1)) = 0 := by 
    nlinarith [sq_nonneg (α^2 - α - c), sq_nonneg (α^2 + (c + 1)), sq_nonneg (α - (c + 1)), sq_nonneg (α + 1), sq_nonneg (α^2 - c), sq_nonneg (α * c)]

  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- The first factor is zero, so c = α^2 - α
    linarith
  · -- The second factor is zero, so α^2 = -c - 1
    nlinarith [sq_nonneg (α), sq_nonneg (c - α), sq_nonneg (α - 1), sq_nonneg (α + 1), sq_nonneg (c + 1)]