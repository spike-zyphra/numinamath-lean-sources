import Mathlib

theorem algebra_16029 {a b c : ℝ} (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 2)
    (h₂ : a^3 + b^3 + c^3 = 3) :
    a^4 + b^4 + c^4 = 25 / 6 := by

  have h₃ : a * b + b * c + c * a = -1 / 2 := by
    have eq1 : a^2 + b^2 + c^2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by 
      ring
    rw [h₀] at eq1
    linarith [h₁, eq1]

  have h₄ : a * b * c = 1 / 6 := by
    have eq2 : a^3 + b^3 + c^3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by 
      ring
    rw [h₀, h₃] at eq2
    linarith [h₂, eq2]

  have h₅ : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 = -1 / 12 := by
    have eq3 : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 = (a * b + b * c + c * a) ^ 2 - 2 * (a * b * c) * (a + b + c) := by 
      ring
    rw [h₃, h₄, h₀] at eq3
    linarith [eq3]

  have eq4 : a^4 + b^4 + c^4 = (a^2 + b^2 + c^2) ^ 2 - 2 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) := by 
    ring

  rw [eq4, h₁, h₅]
  norm_num