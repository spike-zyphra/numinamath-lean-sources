import Mathlib

/- Solve the equation $|y-6| + 2y = 9$ for $y$. -/
theorem algebra_10230 : {y : ℝ | abs (y - 6) + 2 * y = 9} = {3} := by
  ext y
  simp
  constructor
  intro h
  cases' abs_cases (y - 6) with h₁ h₁
  linarith
  linarith
  intro h
  rw [h]
  norm_num
