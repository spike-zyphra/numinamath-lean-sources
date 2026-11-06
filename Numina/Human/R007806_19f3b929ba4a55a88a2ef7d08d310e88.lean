import Mathlib

/- An elephant and a lion are currently 1 mile apart. The elephant runs directly away from the lion at 19 miles per hour, while the lion runs directly towards the elephant at 24 miles per hour.  How many minutes will it take for the lion to catch the elephant? -/
theorem algebra_20996 (t : ℝ) (ht : t > 0) (h : 24 * t - 19 * t = 1) :
    t * 60 = 12 := by linarith
