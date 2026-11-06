import Mathlib

/- The rails on a railroad are 30 feet long. As the train passes over the point where the rails are joined, there is an 
audible click. The speed of the train in miles per hour is approximately the number of clicks heard in:
(A) 20 seconds (B) 2 minutes (C) 112 minutes (D) 5 minutes (E) none of these-/

-- The time t in seconds is given by the number of miles in 30 feet (30 / 5280) times the number of seconds per hour (60 * 60).
-- This evaluates to 20 + 5 / 11 seconds, which is approximately 20 seconds.

theorem algebra_94934 (t : ℝ) (h : t = 60 * 60 * 30 / 5280):
t = 20 + 5 / 11 := by {
  norm_num at h
  norm_num
  exact h
}