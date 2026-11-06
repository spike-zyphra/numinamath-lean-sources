import Mathlib

/- Susie Q has 1000 dollars to invest.  She invests some of the money at the Pretty Penny Bank, which compounds annually at 3 percent.  She invests the rest of the money at the Five and Dime Bank, which compounds annually at 5 percent.  After two years, Susie has a total of $\$1090.02$.  How much did Susie Q originally invest at the Pretty Penny Bank, in dollars? -/
theorem algebra_13359 {x y : ℝ} (hx : x + y = 1000) (hy : (1 + 3 / 100) ^ 2 * x + (1 + 5 / 100) ^ 2 * y = 1090.02) :
    x = 300 := by
  ring_nf at hx hy
  nlinarith