import Mathlib

/- A shirt's sale price is marked $\$14.40$, which is $60\%$ off the original price. How many dollars was the original price of the shirt? -/
theorem algebra_19992 {x : ℝ} (h : x * 0.4 = 14.40) : x = 36 := by 
  norm_num at h
  linarith