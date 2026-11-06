import Mathlib

theorem algebra_297102 (x : ℝ) (hx : x < -1) : 2 - abs (2 - abs (x - 2)) = 2 + x := by
  have h1 : abs (x - 2) = -(x - 2) := by
    have h2 : x - 2 < 0 := by linarith
    rw [abs_of_neg h2]
  have h3 : 2 - abs (x - 2) = x := by
    rw [h1]
    ring
  have h4 : abs (2 - abs (x - 2)) = -x := by
    rw [h3]
    have h5 : x < 0 := by linarith
    rw [abs_of_neg h5]
    all_goals linarith
  rw [h4]
  all_goals linarith