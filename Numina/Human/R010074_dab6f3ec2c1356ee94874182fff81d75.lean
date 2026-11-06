import Mathlib
open Real Set

/- Given that $x$ and $y$ are positive numbers that satisfy the equation $2x + y = 20$, find the maximum value of $\lg x + \lg y$. -/
theorem algebra_9159 : IsGreatest
  {z | ∃ x y, x > 0 ∧ y > 0 ∧ 2*x + y = 20 ∧ z = logb 10 x + logb 10 y} (2 - logb 10 2) := by
  -- We need to prove two things:
  -- 1. 2 - log_10(2) can be achieved
  -- 2. For any x, y > 0 such that 2x + y = 20, log_10(x) + log_10(y) ≤ 2 - log_10(2)
  constructor
  . -- Set x = 5 and y = 10
    use 5, 10
    norm_num
    suffices _ : logb 10 2 + logb 10 5 = 1 by linarith
    -- log_10(2) + log_10(5) = log_10(10) = 1
    rw [← logb_mul (by norm_num) (by norm_num), show 2 * 5 = (10 : ℝ) by norm_num, logb_self_eq_one (by norm_num)]
  . rintro z ⟨x, y, hx, hy, hxy, rfl⟩
    -- Rewrite 2 - log_10(2) as log_10(50)
    have h1 : 2 - logb 10 2 = logb 10 50 := by
      suffices _ : logb 10 2 + logb 10 50 = 2 by linarith
      -- log_10(2) + log_10(50) = log_10(100) = 2
      rw [← logb_mul (by norm_num) (by norm_num), show 2 * 50 = (10 ^ (2 : ℝ) : ℝ) by norm_num, logb_rpow (by norm_num) (by norm_num)]
    rw [h1]
    clear h1
    -- log_10(x) + log_10(y) = log_10(x * y) ≤ log_10(50)
    rw [← logb_mul (by positivity) (by positivity), logb_le_logb (by norm_num) (by positivity) (by positivity)]
    -- x * y ≤ 50 by (x - 5)^2 ≥ 0
    nlinarith [sq_nonneg (x - 5)]
