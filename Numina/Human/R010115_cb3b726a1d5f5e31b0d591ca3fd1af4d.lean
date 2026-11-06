import Mathlib

/- The points $(-3,2)$ and $(-2,3)$ lie on a circle whose center is on the $x$-axis. What is the radius of the circle? -/
theorem algebra_19634 (x : ℝ) (h : (x + 3)^2 + 2^2 = (x + 2)^2 + 3^2) :
    Real.sqrt ((x + 3)^2 + 2^2) = Real.sqrt 13 := by
  -- Note on formalization of the problem:
  -- Let the center of the circle be (x, 0)
  -- Then the distance from the center to (-3, 2) is the same as the distance from the center to (-2, 3)
  -- Translated as (x + 3)^2 + 2^2 = (x + 2)^2 + 3^2
  -- The radius is the distance from the center to (-3, 2), which is sqrt((x + 3)^2 + 2^2)

  -- The condition h is actually a linear equation, so we can solve for x using linarith
  replace h : x = 0 := by linarith
  -- Substitute x = 0 into the expression for the radius
  subst x
  -- Simplify the expression for the radius
  norm_num
