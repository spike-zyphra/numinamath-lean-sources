import Mathlib

/- Triangle $ABC$ has sides of $6$ units, $8$ units, and $10$ units. The width of a rectangle, whose area is equal to the area of the triangle, is $4$ units. What is the perimeter of this rectangle, in units? -/
theorem algebra_11539 (a b c : ℝ) (h₀ : a = 6) (h₁ : b = 8) (h₂ : c = 10)
    (h₃ : d * 4 = (1 / 2) * a * b) :
    2 * (d + 4) = 20 := by
  rw [h₀, h₁] at h₃
  linarith