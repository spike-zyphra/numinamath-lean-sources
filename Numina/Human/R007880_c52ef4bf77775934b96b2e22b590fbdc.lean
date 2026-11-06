import Mathlib

/- In a right triangle with integer length sides, the hypotenuse has length 39 units. How many units is the length of the shorter leg? -/
theorem algebra_10823 (a b c : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 39) :
    min a b = 15 := by
  rw [h₄] at h₃
  norm_num at h₃
  have : a ≤ 39 := by nlinarith
  have : b ≤ 39 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega