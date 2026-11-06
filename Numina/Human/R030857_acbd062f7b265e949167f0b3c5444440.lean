import Mathlib

/- The hypotenuse of a right triangle measures 10 inches and one angle is $45^{\circ}$. What is the number of square inches in the area of the triangle? -/
theorem algebra_11549 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 10) (h₅ : a / b = 1) :
    (1 / 2) * a * b = 25 := by 
  have h₆ : a = b := by
    apply eq_of_div_eq_one
    linarith [h₅]
  rw [h₆] at h₃
  nlinarith [h₀, h₁, h₂, h₃, h₄]