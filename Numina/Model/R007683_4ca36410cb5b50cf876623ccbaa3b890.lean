import Mathlib

theorem algebra_10897 {x p : ℝ} (hx : x < 2) (hxp : abs (x - 2) = p) :
    x - p = 2 - 2 * p := by
  have h1 : x - 2 < 0 := by
    linarith
  rw [abs_of_neg h1] at hxp
  have hx2 : x = 2 - p := by linarith
  rw [hx2]
  ring