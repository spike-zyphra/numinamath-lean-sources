import Mathlib

theorem algebra_184417 {a b c : ℝ} (h₀ : a + b + c = 100) (h₁ : a * b + b * c + c * a = 20)
    (h₂ : (a + b) * (a + c) = 24) :
    b * c = 224 ∨ b * c = -176 := by
  have h3 : a ^ 2 = 4 := by
    have eq1 : (a + b) * (a + c) = a ^ 2 + (a * b + b * c + c * a) := by 
      ring
    rw [eq1] at h₂
    nlinarith [h₁, h₂]

  have ha1 : a = 2 ∨ a = -2 := by 
    have h4 : a ^ 2 = 4 := h3
    have h5 : a = 2 ∨ a = -2 := by
      have h6 : a ^ 2 - 4 = 0 := by linarith
      have h7 : (a - 2) * (a + 2) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.1 h7) with
      | inl h8 => 
        left
        linarith
      | inr h9 => 
        right
        linarith
    exact h5
  
  cases ha1 with
  | inl ha2 =>
    have h4 : b + c = 98 := by
      have h5 : a = (2 : ℝ) := ha2
      linarith [h₀, h5]
    have h5 : b * c = -176 := by
      have ha2' : a = (2 : ℝ) := ha2
      have h6 : a * b + b * c + c * a = 20 := h₁
      rw [ha2'] at h6
      have h7 : 2 * b + b * c + 2 * c = 20 := by
        linarith
      have h7' : 2 * (b + c) + b * c = 20 := by 
        linarith 
      rw [show b + c = (98 : ℝ) by linarith] at h7'
      linarith
    right
    linarith
  | inr ha2 =>
    have h4 : b + c = 102 := by
      have h5 : a = (-2 : ℝ) := ha2
      linarith [h₀, h5]
    have h5 : b * c = 224 := by
      have ha2' : a = (-2 : ℝ) := ha2
      have h6 : a * b + b * c + c * a = 20 := h₁
      rw [ha2'] at h6
      have h7 : -2 * b + b * c - 2 * c = 20 := by
        linarith 
      have h8 : -2 * (b + c) + b * c = 20 := by
        linarith
      rw [show b + c = (102 : ℝ) by linarith] at h8
      linarith
    left
    linarith