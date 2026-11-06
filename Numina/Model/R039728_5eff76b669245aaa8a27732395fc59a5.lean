import Mathlib
open Real

theorem algebra_97493 (x : ℝ) (hx : x < -2) : abs (1 - abs (1 + x)) = -2 - x := by
  have h1 : 1 + x < 0 := by linarith
  have h2 : abs (1 + x) = - (1 + x) := by
    rw [abs_of_neg h1]
  have h3 : 1 - abs (1 + x) = 2 + x := by
    rw [h2]
    linarith
  rw [h3]
  have h4 : (2 + x : ℝ) < 0 := by linarith
  rw [abs_of_neg h4]
  all_goals linarith