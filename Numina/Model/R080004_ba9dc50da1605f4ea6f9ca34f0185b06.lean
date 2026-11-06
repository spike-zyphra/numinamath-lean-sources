import Mathlib

theorem algebra_198538 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (hxy : x = y - 5) (hxy' : x * 30 = y * 20) :
    x * 6 = y * 4 := by 
  rw [hxy] at hxy' -- Substitute x with (y - 5) in the equation
  -- Use linear arithmetic solver to complete the goal
  linarith