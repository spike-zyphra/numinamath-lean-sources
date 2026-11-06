import Mathlib

/- What is the integer value of $x$ in the arithmetic sequence $3^2, x, 3^4$? -/
theorem algebra_21843 (x : ℤ) (h : ∃ d, x = 3^2 + d ∧ x = 3^4 - d) : x = 45 := by 
  cases' h with d h
  omega