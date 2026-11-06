import Mathlib

/- Bao was given $\$1,\!000$ for his birthday. He decided to invest the money in a bank account that earns $10\%$ interest, compounded annually. In dollars, how much total interest will Bao have earned 3 years later? -/
theorem algebra_13751 (P : ℝ) (r : ℝ) (t : ℝ) (hP : P = 1000) (hr : r = 0.1) (ht : t = 3) :
    P * (1 + r) ^ t - P = 331 := by
  rw [hP, hr, ht]; norm_num