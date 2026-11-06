import Mathlib

/- The largest and smallest of three consecutive terms in an arithmetic sequence differ by 14. Half of the smallest term is added to each term and the sum of the resulting three numbers is 120. What is the value of the original smallest term? -/
theorem algebra_21989 (a d : ℝ) (h₁ : a + 14 = a + 2 * d) (h₂ : (a / 2 + a) + (a / 2 + a + d) + (a / 2 + a + d * 2) = 120) :
    a = 22 := by linarith
