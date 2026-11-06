import Mathlib

/- A right triangle has an area of 120 square units, and a leg length of 24 units. What is the perimeter of the triangle, in units? -/
theorem algebra_15431 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : 120 = (1/2) * a * b) (h₅ : a = 24) :
    a + b + c = 60 := by
  subst h₅
  nlinarith