import Mathlib

/- A robot moving forward at a constant speed takes 2.5 hours to travel 1 kilometer. Moving forward at this same constant speed, it takes the robot 90 seconds to travel the length of a particular hallway. How many meters long is the hallway? -/
theorem algebra_21882 (v : ℝ) (h : v = 1 / 2.5) (l : ℝ) (hl : l / v = 90 / 3600) :
    l * 1000 = 10 := by
  subst_vars
  norm_num at hl
  linarith
