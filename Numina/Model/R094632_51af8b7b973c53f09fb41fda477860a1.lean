import Mathlib

theorem algebra_93219 (x : ℝ) (hx : x < 0) :
    abs (x - Real.sqrt ((x - 1)^2)) = 1 - 2 * x := by
  have h1 : Real.sqrt ((x - 1) ^ 2) = |x - 1| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1]
  have h2 : x - 1 < 0 := by linarith
  rw [abs_of_neg h2]
  have h3 : x - (-(x - 1)) = 2 * x - 1 := by ring
  rw [h3]
  have h4 : (2 * x - 1) < 0 := by linarith
  rw [abs_of_neg h4]
  ring