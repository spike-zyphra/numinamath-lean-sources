import Mathlib

/- The CCA Math Banana$^{\text{TM}}$ costs \$$100$. The cost rises $10$% then drops $10$%. Now what is the cost of the CCA Math Banana$^{\text{TM}}$?

[i]2018 CCA Math Bonanza Lightning Round #1.2[/i] -/
theorem algebra_70863 (x : ℝ) (hx : x = 100) :
    (x * 1.1) * 0.9 = 99 := by
  -- Start with the original price of 100 dollars.
  norm_num [hx]
