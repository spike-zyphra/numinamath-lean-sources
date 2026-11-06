import Mathlib

/- The average of the five numbers in a list is 54. The average of the first two numbers is 48. What is the average of the last three numbers? -/
theorem algebra_12590 (a b c d e : ℝ) (h₀ : (a + b + c + d + e) / 5 = 54) (h₁ : (a + b) / 2 = 48) :
    (c + d + e) / 3 = 58 := by 
  nlinarith