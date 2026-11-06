import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_251743 {x : ℝ} (hx : 0 ≤ x) :
    abs ((x^2 - 6 * sqrt x + 7) / (x^2 + 6 * sqrt x + 7)) = 1 ↔ x = 0 := by
  constructor
  · -- Assume abs ((x^2 - 6 * sqrt x + 7) / (x^2 + 6 * sqrt x + 7)) = 1, prove x = 0
    intro h
    have h1 : abs ((x^2 - 6 * sqrt x + 7) / (x^2 + 6 * sqrt x + 7)) = 1 := h
    have h2 : (x^2 - 6 * sqrt x + 7) / (x^2 + 6 * sqrt x + 7) = 1 ∨ (x^2 - 6 * sqrt x + 7) / (x^2 + 6 * sqrt x + 7) = -1 := by 
      cases eq_or_eq_neg_of_abs_eq h1 with
      | inl h3 =>
        left
        linarith
      | inr h3 =>
        right
        linarith
    rcases h2 with h2 | h2 
    · -- Assume the fraction equals 1 
      have h3 : x^2 + 6 * sqrt x + 7 > 0 := by 
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show x ≥ 0 by linarith), sq_nonneg (sqrt x), sq_nonneg (x), Real.sqrt_nonneg x]
      have h4 : x^2 - 6 * sqrt x + 7 = x^2 + 6 * sqrt x + 7 := by 
        have h5 : x^2 + 6 * sqrt x + 7 > 0 := h3 
        field_simp at h2 ⊢ 
        nlinarith 
      have h5 : -6 * sqrt x = 6 * sqrt x := by 
        nlinarith 
      have h6 : sqrt x = 0 := by 
        nlinarith 
      have h7 : x = 0 := by 
        rw [Real.sqrt_eq_zero (by linarith)] at h6 
        linarith 
      exact h7 
    · -- Assume the fraction equals -1 
      have h3 : x^2 + 6 * sqrt x + 7 > 0 := by 
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show x ≥ 0 by linarith), sq_nonneg (sqrt x), sq_nonneg (x), Real.sqrt_nonneg x]
      have h4 : x^2 - 6 * sqrt x + 7 = - (x^2 + 6 * sqrt x + 7) := by 
        have h5 : x^2 + 6 * sqrt x + 7 > 0 := h3 
        field_simp at h2 ⊢ 
        nlinarith 
      have h5 : x^2 - 6 * sqrt x + 7 + (x^2 + 6 * sqrt x + 7) = 0 := by 
        linarith [h4] 
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show x ≥ 0 by linarith), sq_nonneg (sqrt x), sq_nonneg (x), Real.sqrt_nonneg x]
  · -- Assume x = 0, prove abs ((x^2 - 6 * sqrt x + 7) / (x^2 + 6 * sqrt x + 7)) = 1
    intro h 
    rw [h] 
    have h3 : sqrt (0 : ℝ) = 0 := by 
      simp 
    rw [h3] 
    norm_num [abs_of_nonneg]