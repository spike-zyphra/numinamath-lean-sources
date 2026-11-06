import Mathlib

theorem algebra_114420 (a b c : ℝ) (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 2)
    (h₂ : a^3 + b^3 + c^3 = 3) :
    a * b * c = 1 / 6 ∧ a^4 + b^4 + c^4 = 25 / 6 := by 
  have h₃ : a*b + b*c + c*a = -1/2 := by
    have h : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2*(a*b + b*c + c*a) := by 
      ring
    rw [h₀, h₁] at h 
    linarith

  have h₄ : a*b*c = 1/6 := by
    have eq : a^3 + b^3 + c^3 = (a + b + c)^3 - 3*(a + b + c)*(a*b + b*c + c*a) + 3*(a*b*c) := by 
      ring
    have eq1 := eq
    simp only [h₀, h₃, h₂] at eq1
    linarith 

  have h₅ : a^4 + b^4 + c^4 = 25/6 := by
    have h₆ : a * b * c = 1 / 6 := h₄
    have h₇ : a*b + b*c + c*a = -1/2 := h₃
    have eq1 : a^2*b^2 + b^2*c^2 + c^2*a^2 = -1/12 := by
      have h : (a*b + b*c + c*a) ^ 2 = a^2*b^2 + b^2*c^2 + c^2*a^2 + 2*(a*b*c)*(a + b + c) := by
        ring
      rw [show a*b + b*c + c*a = -1/2 by linarith [h₇], show a*b*c = 1/6 by linarith [h₆], show a + b + c = 1 by linarith [h₀]] at h
      linarith

    have h₈ : a^4 + b^4 + c^4 = (a^2 + b^2 + c^2)^2 - 2*(a^2*b^2 + b^2*c^2 + c^2*a^2) := by
      ring

    rw [h₈, h₁, eq1]
    norm_num

  constructor
  · exact h₄
  · exact h₅