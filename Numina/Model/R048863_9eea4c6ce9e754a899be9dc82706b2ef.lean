import Mathlib

theorem algebra_6270 {a b : ℤ} (h₀ : a + b = 8) (h₁ : a^2 + b^2 = 34) (h₂ : a > b) : a - b = 2 := by 
  have h3 : a * b = 15 := by
    have h4 : a + b = 8 := h₀
    have h5 : a^2 + b^2 = 34 := h₁
    have h6 : (a + b)^2 = a^2 + 2 * (a * b) + b^2 := by 
      ring
    rw [h4] at h6
    nlinarith [h5, h6]
  have h4 : a = 5 ∨ a = 3 := by
    have h5 : a + b = 8 := h₀
    have h6 : a * b = 15 := h3
    have h7 : b = 8 - a := by linarith
    rw [h7] at h6
    have h8 : a^2 - 8 * a + 15 = 0 := by
      nlinarith
    have : (a - 5) * (a - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp this) with h7 h8
    · left
      linarith
    · right
      linarith
  cases h4 with
  | inl h5 =>
    have h6 : b = 3 := by linarith
    linarith
  | inr h5 =>
    have h6 : b = 5 := by linarith
    linarith