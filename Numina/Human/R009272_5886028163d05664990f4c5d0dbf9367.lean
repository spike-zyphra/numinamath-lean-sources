import Mathlib

/- The average of Amy's, Ben's, and Chris's ages is 9. Four years ago,  Chris was the same age as Amy is now. In 3 years, Ben's age will be $\frac{2}{3}$ of Amy's age at that time. How many years old is Chris now? -/
theorem algebra_12813 (a b c : ℝ) (h' : a > 0 ∧ b > 0 ∧ c > 0) (h₀ : (a + b + c) / 3 = 9)
    (h₁ : c - 4 = a) (h₂ : b + 3 = (2 / 3) * (a + 3)) :
    c = 13 := by
  linarith
