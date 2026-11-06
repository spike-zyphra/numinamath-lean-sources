import Mathlib

/- On Tuesday, I worked $t+1$ hours and earned $3t-3$ dollars per hour. My friend Andrew worked $3t-5$ hours but only earned $t+2$ dollars an hour. At the end of the day, I had earned two dollars more than he had. What is the value of $t$? -/
theorem algebra_13128 (t : ℝ) (ht : t > 5 / 3) (h : (t + 1) * (3 * t - 3) = (3 * t - 5) * (t + 2) + 2) :
    t = 5 := by
  ring_nf at h
  linarith
