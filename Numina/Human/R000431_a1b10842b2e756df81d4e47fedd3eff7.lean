import Mathlib

/- Working 22 hours in the second week of June, Xenia was able to earn $\$$47.60 more than during the first week of June when she worked 15 hours. If her hourly wage was constant, how many dollars did she earn during the first two weeks of June? Express your answer to the nearest hundredth.-/

theorem algebra_10526 (x : ℝ) (h : 22 * x = 15 * x + 47.60) : 37 * x = 251.60 := by
  have : x = 6.80 := by
    linarith
  rw [this]
  norm_num
