import Mathlib

theorem algebra_325316 (a b c : ℝ) (h₀ : a^2 - b * c - 8 * a + 7 = 0) (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by
  have eq1 : (b + c) ^ 2 = (a - 1) ^ 2 := by
    have hbc : b * c = a^2 - 8 * a + 7 := by
      nlinarith
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), hbc]
  
  have h2 : b + c = a - 1 ∨ b + c = 1 - a := by
    have h : (b + c - (a - 1)) * (b + c - (1 - a)) = 0 := by
      nlinarith [eq1]
    cases' (mul_eq_zero.mp h) with h3 h4
    · left
      linarith
    · right
      linarith
  
  cases h2 with
  | inl h2 =>
    have hbc : b * c = a^2 - 8 * a + 7 := by
      nlinarith
    have h4 : (a - 1)^2 - 4 * (a^2 - 8 * a + 7) ≥ 0 := by
      nlinarith [sq_nonneg (b - c), h2, hbc]
    
    have h5 : a ^ 2 - 10 * a + 9 ≤ 0 := by
      nlinarith
    
    constructor
    · nlinarith
    · nlinarith
  
  | inr h2 =>
    have hbc : b * c = a^2 - 8 * a + 7 := by
      nlinarith
    have h4 : (1 - a)^2 - 4 * (a^2 - 8 * a + 7) ≥ 0 := by
      nlinarith [sq_nonneg (b - c), h2, hbc]
    
    have h5 : a ^ 2 - 10 * a + 9 ≤ 0 := by
      nlinarith
    
    constructor
    · nlinarith
    · nlinarith