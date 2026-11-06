import Mathlib

/- What is the sum of the even, positive integers less than 62? -/
theorem algebra_14058 : ∑ x in (Finset.Ico 1 62).filter Even, x = 930 := by
  rfl