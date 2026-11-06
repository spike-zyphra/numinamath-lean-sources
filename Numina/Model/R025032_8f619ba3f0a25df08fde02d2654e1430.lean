import Mathlib

theorem algebra_2213 (a b : ℝ) (h₀ : a ≥ 0) (h₁ : b ≥ 0) : (a^2 = b^2 → a = b) ∧ (a^3 = b^3 → a = b) := by
  constructor
  · -- First implication: if a^2 = b^2 then a = b
    intro h
    have h2 : a = b := by
      have h3 : a ^ 2 = b ^ 2 := h
      have h4 : a ^ 2 - b ^ 2 = 0 := by linarith
      have h5 : (a - b) * (a + b) = 0 := by
        ring_nf at h4 ⊢
        linarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- Case where $a - b = 0$
        linarith
      · -- Case where $a + b = 0$
        have h8 : a + b = 0 := by linarith
        have h9 : a = 0 := by nlinarith
        have h10 : b = 0 := by nlinarith
        linarith
    linarith
  · -- Second implication: if a^3 = b^3 then a = b
    intro h
    have h3 : a ^ 3 = b ^ 3 := h
    have h4 : a ^ 3 - b ^ 3 = 0 := by linarith
    have h5 : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case where $a - b = 0$
      linarith
    · -- Case where $a^2 + a * b + b^2 = 0$
      have h8 : a ^ 2 + a * b + b ^ 2 = 0 := by linarith
      have h9 : a = 0 := by 
        nlinarith [sq_nonneg (a), sq_nonneg (b), mul_nonneg h₀ h₁]
      have h10 : b = 0 := by 
        nlinarith [sq_nonneg (a), sq_nonneg (b), mul_nonneg h₀ h₁]
      linarith