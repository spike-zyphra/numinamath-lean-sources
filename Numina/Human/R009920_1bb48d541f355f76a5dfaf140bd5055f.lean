import Mathlib

/- Paula invests $\$10,\!000$ at the start of a 5 year period at an interest rate of $10\%$. At the end of those 5 years, how much is her investment worth if the interest is compounded quarterly?  Express your answer rounded to the nearest cent. -/
theorem algebra_19869 (invest : ℝ) (rate : ℝ) (time : ℝ) (hP : invest = 10000) (hr : rate = 0.1) (ht : time = 5)
    (h : invest * (1 + rate / 4) ^ (4 * time) = x) :
    (round (100 * x) : ℝ) * 100⁻¹ = 16386.16 := by
  rw [h.symm, hP, hr, ht]
  norm_num [round, Int.fract]