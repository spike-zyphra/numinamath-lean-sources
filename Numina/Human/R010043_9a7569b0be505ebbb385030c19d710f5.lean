import Mathlib

/- Bill buys a stock that decreases by $20\%$ on the first day, and then  on the second day the stock increases by $30\%$ of its value at the end of the first day. What was the overall percent increase in Bill's stock over the two days? -/
theorem algebra_16498 {x y : ℝ} (hx : x = -20 / 100) (hy : y = 30 / 100) :
    (1 + x) * (1 + y) - 1 = 4 / 100 := by
  rw [hx, hy]
  ring