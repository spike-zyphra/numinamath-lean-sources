import Mathlib

/- A stock loses $10\%$ of its value on Monday.  On Tuesday it loses  $20\%$ of the value it had at the end of the day on Monday.  What is  the overall percent loss in value from the beginning of Monday to  the end of Tuesday?  Enter the answer as a percent. -/
theorem algebra_20237 {x y : ℝ} (hx : x = 0.9) (hy : y = 0.8) :
    (1 - x * y) * 100 = 28 := by 
  norm_num [hx, hy]