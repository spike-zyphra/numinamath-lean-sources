import Mathlib

open Finset Real

/-Which is greater: $2^{100!}$ or $(2^{100})!$? Compare these two values by evaluating their base-2 logarithms and determining the relationship between $100!$ and $\sum_{k=1}^{2^{100}} \log_2 k$.-/
theorem number_theory_611819 (hn : n = 100) : Nat.factorial (2 ^ n) < 2 ^ Nat.factorial n := by
-- Apply $(2^n)!≤(2^n)^(2^n)$ and simplify  
  apply lt_of_le_of_lt (Nat.factorial_le_pow (2 ^ n))
  rw [← pow_mul, pow_lt_pow_iff_right₀]
  nth_rw 3 [show n = n-1+1 by omega]
  rw [Nat.factorial_succ, Nat.sub_add_cancel]
  rw [mul_lt_mul_left]; rify
-- `rify` the goal and take log-base $2$ both sides
  rw [← rpow_natCast, ← lt_logb_iff_rpow_lt]
  norm_num [hn]; rw [← prod_range_add_one_eq_factorial]
  push_cast; rw [show 99 = 3+96 by rfl, prod_range_add]
  rw [logb_mul]; calc
    -- Splite the product at $4$
    _ < logb 2 (∏ x ∈ range 3, (x + 1)) + logb 2 (∏ x ∈ range 96, 2 ^ 2) := by
      rw [prod_const, ← pow_mul, logb_pow]
      norm_num; have : 0 ≤ logb 2 6 := by
        apply logb_nonneg; all_goals norm_num
      linarith only [this]
    -- Since $logb 2 (i+4)$ is at least $2$, the inequality holds true
    _ ≤ _ := by
      gcongr with i hi; norm_num
      norm_cast; omega
  any_goals positivity
  any_goals norm_num
  simp [hn]