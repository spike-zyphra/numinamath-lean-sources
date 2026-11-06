import Mathlib

/- Given that $x < 5$, rewrite $5x - |x - 5|$ without using absolute value signs. -/
theorem algebra_20071 (x : ℝ) (hx : x < 5) : 5 * x - abs (x - 5) = 6 * x - 5 := by 
  cases' abs_cases (x - 5) with h h <;> linarith