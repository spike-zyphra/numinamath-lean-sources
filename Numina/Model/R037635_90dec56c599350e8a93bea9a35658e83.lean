import Mathlib

theorem algebra_300285 (a b c : ℝ)
    (h₀ : a^2 + b^2 + c^2 - 10 * a - 11 = 0)
    (h₁ : a^2 - b * c - 4 * a - 5 = 0) :
    a * b + b * c + c * a ∈ Set.Icc (-40) 72 := by
  have h2 : b ^ 2 + c ^ 2 + b * c = 6 * a + 6 := by
    nlinarith
  have h3 : b * c = a^2 - 4 * a - 5 := by
    nlinarith
  have h4 : (b + c) ^ 2 = (a + 1) ^ 2 := by
    nlinarith [h2, h3]
  have h5 : b + c = a + 1 ∨ b + c = - (a + 1) := by
    have h6 : (b + c) ^ 2 - (a + 1) ^ 2 = 0 := by
      linarith [h4]
    have h7 : (b + c - (a + 1)) * (b + c + (a + 1)) = 0 := by
      nlinarith [h6]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- b + c - (a + 1) = 0
      left
      linarith
    · -- b + c + (a + 1) = 0 
      right
      nlinarith 
  cases h5 with
  | inl h5 =>
    have h6 : a * b + b * c + c * a = 2 * a^2 - 3 * a - 5 := by
      have h7 : b + c = a + 1 := h5
      have h8 : a * b + b * c + c * a = a * (b + c) + b * c := by 
        ring
      rw [h8]
      rw [h7, h3]
      nlinarith 
    rw [h6]
    constructor 
    · -- Show that -40 ≤ 2 * a^2 - 3 * a - 5
      nlinarith [sq_nonneg (a - 4), sq_nonneg (a + 3), sq_nonneg (b - c), sq_nonneg (a + 1), sq_nonneg (b + c), sq_nonneg (a - 5)]
    · -- Show that 2 * a^2 - 3 * a - 5 ≤ 72 
      nlinarith [sq_nonneg (a - 4), sq_nonneg (a + 3), sq_nonneg (b - c), sq_nonneg (a + 1), sq_nonneg (b + c), sq_nonneg (a - 5)]
  | inr h5 =>
    have h7 : a * b + b * c + c * a = -5 * a - 5 := by 
      have h8 : a * b + b * c + c * a = a * (b + c) + b * c := by
        ring 
      rw [h8]
      rw [show b + c = - (a + 1) by linarith [h5], h3]
      nlinarith 
    rw [h7]
    constructor 
    · -- Show that -40 ≤ -5 * a - 5 
      nlinarith [sq_nonneg (a - 4), sq_nonneg (a + 3), sq_nonneg (b - c), sq_nonneg (a + 1), sq_nonneg (b + c), sq_nonneg (a - 5)]
    · -- Show that -5 * a - 5 ≤ 72 
      nlinarith [sq_nonneg (a - 4), sq_nonneg (a + 3), sq_nonneg (b - c), sq_nonneg (a + 1), sq_nonneg (b + c), sq_nonneg (a - 5)]