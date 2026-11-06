import Mathlib

/- After two years, at a 4.5 percent annual interest rate, the investment will have grown to $10000 \cdot (1.045)^2 = 10920.25$, so the interest earned is $10920.25 - 10000 = \boxed{920.25}$. -/
theorem algebra_21769 (deposit : ℝ) (rate : ℝ) (time : ℝ) (hd : deposit = 10000) (hr : rate = 0.045) (ht : time = 2) :
    deposit * (1 + rate) ^ time - deposit = 920.25 := by
  rw [hd, hr, ht]
  norm_num