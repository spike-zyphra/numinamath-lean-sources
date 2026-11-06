import Mathlib

/- Evaluate the infinite geometric series: $$\frac{1}{3}+\frac{1}{6}+\frac{1}{12}+\frac{1}{24}+\dots$$ -/
theorem algebra_15079 : ∑' n : ℕ, (1 / 3 : ℝ) * (1 / 2) ^ n = 2 / 3 := by
  apply HasSum.tsum_eq
  -- The sum is a geometric series with first term 1/3 and common ratio 1/2
  rw [show (2 / 3 : ℝ) = (1 / 3 : ℝ) • 2 by norm_num]
  -- It suffices to show that the sum of the series (1/2)^n is 2
  apply HasSum.const_smul
  nth_rw 2 [show 2 = (1 - (1 / 2) : ℝ)⁻¹ by norm_num]
  -- Use the formula for the sum of a geometric series
  -- If 0 ≤ r < 1, the sum of the series is 1 / (1 - r)
  apply hasSum_geometric_of_lt_one
  all_goals
    norm_num
