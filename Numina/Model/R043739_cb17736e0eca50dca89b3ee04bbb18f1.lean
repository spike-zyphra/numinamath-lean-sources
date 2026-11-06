import Mathlib

theorem algebra_211789 (a b c : ℤ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : a ≠ c) :
    4 * (a^2 + b^2 + c^2) - (a + b + c)^2 ≥ 8 := by
  have h3 : (a - b : ℤ) ^ 2 ≥ 1 := by
    have h4 : a - b ≠ 0 := by 
      intro h5
      apply h₀ 
      omega
    have h5 : (a - b : ℤ) ^ 2 > 0 := by 
      apply sq_pos_of_ne_zero 
      exact h4
    linarith
  have h4 : (b - c : ℤ) ^ 2 ≥ 1 := by 
    have h5 : b - c ≠ 0 := by 
      intro h6 
      apply h₁
      omega
    have  h6 : (b - c : ℤ) ^ 2 > 0 := by 
      apply sq_pos_of_ne_zero 
      exact h5
    linarith
  have h5 : (a - c : ℤ) ^ 2 ≥ 1 := by 
    have h6 : a - c ≠ 0 := by 
      intro h7 
      apply h₂ 
      omega 
    have h7 : (a - c : ℤ) ^ 2 > 0 := by 
      apply sq_pos_of_ne_zero 
      exact h6 
    linarith
  nlinarith [ sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), 
    sq_nonneg (a - c), sq_nonneg (b - c), 
    sq_nonneg (a + b - 2 * c), sq_nonneg (a - b), sq_nonneg (b - c), 
    sq_nonneg (a - c)]