import Mathlib

/- A divisor of a number is a proper divisor if it is not equal to the number. What is the sum of the proper divisors of $432$? -/
theorem number_theory_15585 : ∑ d in (432 : ℕ).properDivisors, d = 808 := by
  rfl