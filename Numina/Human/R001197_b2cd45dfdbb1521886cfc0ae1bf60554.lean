import Mathlib

/- The circumference of Earth is 40,000 kilometers. How many trips around Earth could you take if you travel one billion meters? -/
theorem algebra_21086 (circumference travel : ℝ) (h1 : circumference = 40000) (h2 : travel = 1000000000 / 1000) :
    travel / circumference = 25 := by
  norm_num [h1, h2]