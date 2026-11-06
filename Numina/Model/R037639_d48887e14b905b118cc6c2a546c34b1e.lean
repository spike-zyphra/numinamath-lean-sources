import Mathlib

theorem algebra_20071 (x : ℝ) (hx : x < 5) : 5 * x - abs (x - 5) = 6 * x - 5 := by
  have h1 : abs (x - 5) = 5 - x := by
    have h2 : x - 5 < 0 := by linarith
    rw [abs_of_neg h2]
    all_goals linarith
  rw [h1]
  all_goals linarith