import Mathlib

theorem algebra_306192 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ n ≥ 2, a ^ n = a + 1 ∧ b ^ (2 * n) = b + 3 * a) :
    a > b ∧ b > 1 := by 
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  norm_num at h2 h3 h4
  all_goals 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]