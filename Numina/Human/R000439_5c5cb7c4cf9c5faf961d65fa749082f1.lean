import Mathlib

/- Joanie takes a $\$6,\!000$ loan to pay for her car.  The annual interest rate on the loan is $12\%$.  She makes no payments for 4 years, but has to pay back all the money she owes at the end of 4 years. How much more money will she owe if the interest compounds quarterly than if the interest compounds annually?  Express your answer as a dollar value to the nearest cent.-/
theorem algebra_422 (P : ℝ) (r : ℝ) (t : ℝ) (hP : P = 6000) (hr : r = 0.12) (ht : t = 4) :
    ((round (100 * (P * (1 + r / 4) ^ (4 * t))) - round (100 * (P * (1 + r) ^ t))) : ℝ ) / 100 = 187.12 := by
  -- substitute the given values
  -- simplify the expression by round x = ⌊x + 1 / 2⌋
  rw [hP, hr, ht, round_eq, round_eq]
  -- simple calculate
  norm_num