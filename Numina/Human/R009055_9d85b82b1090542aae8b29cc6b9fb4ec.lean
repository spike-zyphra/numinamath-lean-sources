import Mathlib

/- What is the largest integer value of $x$ for which $5-4x>17$? -/
theorem algebra_15781 :
    IsGreatest {x : ℤ | 5 - 4 * x > 17} (-4) := by
  -- Separate into two goals: -4 satisfies the equation; and -4 is the largest integer satisfying the equation.
  simp [IsGreatest, upperBounds]
  intro a ha
  linarith
