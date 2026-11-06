import Mathlib

/- The minimum value of the function $y=|x-2|+3$ is ______. -/
theorem algebra_9415 : IsLeast {y | ∃ x : ℝ, y = abs (x - 2) + 3} 3 := by
  -- Expand the definitions and split the goals.
  simp [IsLeast, lowerBounds]
  use 2
  simp
