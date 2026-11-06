import Mathlib

/- In a right-angled triangle, the sum of the squares of the three side lengths is 1800.  What is the length of the hypotenuse of this triangle? -/
theorem algebra_15954 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 + c^2 = 1800) (h₄ : c^2 = a^2 + b^2) :
    c = 30 := by
  nlinarith