import Mathlib

/- When Frederick was born, his grandparents gave him a gift of $\$2000$, which was invested at an interest rate of $5\%$ per year, compounded yearly.  How much money will Frederick have when he collects the money at the age of $18$? Give your answer to the nearest hundredth of a dollar. -/
theorem algebra_10348 (P : ℝ) (hP : P = 2000) (r : ℝ) (hr : r = 0.05) (t : ℕ) (ht : t = 18) :
    round (P * (1 + r) ^ t * 100) / (100 : ℝ) = 4813.24 := by
  subst_vars
  norm_num [round_eq]
