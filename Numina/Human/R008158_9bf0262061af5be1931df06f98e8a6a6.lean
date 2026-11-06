import Mathlib

/- The U.S. produces about 5.5 million tons of apples each year. Of the total, $20\%$ is mixed with other products, with $50\%$ of the remainder used for apple juice and the other $50\%$ sold fresh. How many million tons of apples are used for apple juice? Express your answer as a decimal to the nearest tenth. -/
theorem algebra_11069 (total_apples : ℝ) (h : total_apples = 5.5) :
    (total_apples * (1 - 20 / 100)) * 50 / 100 = 2.2 := by
  norm_num [h]