import Mathlib

/- When Frederick was born, his grandparents gave him a gift of $\$2000$, which was invested at a simple interest rate of $5\%$ per year.  How much money will Frederick have when he can collect the money at the age of $18$?  (Assume no money is added to the account besides the interest.) -/
theorem algebra_22239 {P r t : ℝ} (hP : P = 2000) (hr : r = 0.05) (ht : t = 18) :
    P * (1 + r * t) = 3800 := by 
  rw [hP, hr, ht]; norm_num