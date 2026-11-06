import Mathlib

/- The American Mathematics College is holding its orientation for incoming freshmen. The incoming freshman class contains fewer than $500$ people. When the freshmen are told to line up in columns of $23$, $22$ people are in the last column. When the freshmen are told to line up in columns of $21$, $14$ people are in the last column. How many people are in the incoming freshman class? -/
theorem number_theory_14683 (n : ℕ) (h₀ : n < 500) (h₁ : n % 23 = 22) (h₂ : n % 21 = 14) :
  n = 413 := by 
  omega