import Mathlib

theorem algebra_78855 {c : ℝ} (h : ∃ x, x^2 - 3 * x + c = 0 ∧ (-x)^2 + 3 * (-x) - c = 0) :
    x^2 - 3 * x + c = 0 ↔ x = 0 ∨ x = 3 := by
  rcases h with ⟨x₀, hx₁, hx₂⟩ 
  have h1 : c = 0 := by 
    nlinarith
  constructor 
  · -- Assume x^2 - 3 x + c = 0 then x = 0 ∨ x = 3
    intro h_eq 
    have h_eq' : x ^ 2 - 3 * x = 0 := by 
      have h_c : c = (0 : ℝ) := h1 
      rw [h_c] at h_eq 
      linarith 
    have : x * (x - 3) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp this) with hx hx
    · -- x = 0 
      left 
      linarith 
    · -- x - 3 = 0 ⇒ x = 3 
      right 
      linarith 
  · -- Assume x = 0 ∨ x = 3 then x^2 - 3 x + c = 0 
    rintro (h_eq | h_eq)
    · -- x = 0 
      rw [h_eq] 
      rw [show c = (0 : ℝ) by linarith] 
      norm_num 
    · -- x = 3 
      rw [h_eq] 
      rw [show c = (0 : ℝ) by linarith] 
      norm_num