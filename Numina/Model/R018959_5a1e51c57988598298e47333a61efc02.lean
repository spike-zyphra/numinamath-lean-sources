import Mathlib

open Real

theorem inequalities_4748 (a : ℝ) (h₀ : 0 ≤ a) (b : ℝ) (h₁ : 1 ≤ b) :
    a * b ≤ exp a + b * (log b - 1) := by
  have h4 : exp (a - log b) ≥ (a - log b) + 1 := by
    nlinarith [Real.add_one_le_exp (a - log b)]
  have h5 : exp (log b) = b := by
    rw [Real.exp_log]
    linarith
  have h6 : exp a ≥ b * ( (a - log b) + 1 ) := by
    have h7 : exp a = exp (a - log b) * exp (log b) := by
      rw [← Real.exp_add]
      ring_nf
    have h9 : exp (a - log b) ≥ (a - log b) + 1 := by
      linarith [Real.add_one_le_exp (a - log b)]
    have h9' : exp a ≥ b * ( (a - log b) + 1 ) := by
      rw [h7]
      have h6' : exp (log b) = b := h5
      rw [h6']
      nlinarith [h9, h₁, Real.exp_nonneg (a - log b)]
    linarith
  have h8 : b * (a - log b + 1) = a * b - b * log b + b := by
    ring_nf
  have h7 : a * b ≤ exp a + b * (log b - 1) := by
    nlinarith [h6, h8]
  linarith