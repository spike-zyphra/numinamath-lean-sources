import Mathlib

theorem algebra_143008 {a b : ℝ} (p : ℝ → ℝ)
    (h₀ : ∀ x, p x = x^4 + 3 * x^3 + a * x^2 + b * x + 7)
    (h₁ : p 1 = 2 * 1 + 7) (h₂ : p (-4) = 2 * (-4) + 7) :
    a = -4 ∧ b = 2 := by
  have eq1 : p 1 = 1^4 + 3 * 1^3 + a * 1^2 + b * 1 + 7 := h₀ 1
  rw [eq1] at h₁
  have eq2 : p (-4) = (-4)^4 + 3 * (-4)^3 + a * (-4)^2 + b * (-4) + 7 := h₀ (-4)
  rw [eq2] at h₂
  have h3 : a + b = -2 := by
    nlinarith
  have h4 : 16 * a - 4 * b = -72 := by
    nlinarith
  have ha : a = -4 := by
    nlinarith [h3, h4]
  have hb : b = 2 := by
    nlinarith [h3, ha]
  constructor
  · exact ha
  · exact hb