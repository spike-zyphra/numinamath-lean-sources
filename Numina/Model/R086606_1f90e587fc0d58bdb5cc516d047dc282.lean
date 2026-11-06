import Mathlib

theorem algebra_6896 {a b : ℤ} (h₀ : a + b = 3) (h₁ : a^2 + b^2 = 17) (h₂ : a > b) : a - b = 5 := by
  have h3 : a * b = -4 := by
    have h : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
      linarith [h₀]
    rw [h₀] at h
    nlinarith
  
  have h4 : a = 4 ∨ a = -1 := by
    have h5 : a * b = -4 := h3
    have h6 : b = 3 - a := by linarith
    rw [h6] at h5
    have h_eq : a^2 - 3 * a - 4 = 0 := by
      linarith

    have factored : (a - 4) * (a + 1) = 0 := by
      nlinarith [h_eq]

    cases (mul_eq_zero.mp factored) with
    | inl h1 => 
      left
      linarith 
    | inr h2 => 
      right
      linarith
  
  cases h4 with
  | inl h_a4 =>
    have h_b1 : b = -1 := by 
      linarith 
    linarith 
  | inr h_a1 =>
    have h_b4 : b = 4 := by 
      linarith 
    nlinarith