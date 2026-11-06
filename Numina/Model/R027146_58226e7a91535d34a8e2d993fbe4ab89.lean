import Mathlib

theorem inequalities_38849 (p q r s : ℝ) (h₀ : p + q + r + s = 9) (h₁ : p^2 + q^2 + r^2 + s^2 = 21) :
    ∃ a b c d : ℝ, (a = p ∧ b = q ∧ c = r ∧ d = s) ∨ (a = p ∧ b = q ∧ c = s ∧ d = r) ∨
    (a = p ∧ b = r ∧ c = q ∧ d = s) ∨ (a = p ∧ b = r ∧ c = s ∧ d = q) ∨
    (a = p ∧ b = s ∧ c = q ∧ d = r) ∨ (a = p ∧ b = s ∧ c = r ∧ d = q) ∨
    (a = q ∧ b = p ∧ c = r ∧ d = s) ∨ (a = q ∧ b = p ∧ c = s ∧ d = r) ∨
    (a = q ∧ b = r ∧ c = p ∧ d = s) ∨ (a = q ∧ b = r ∧ c = s ∧ d = p) ∨
    (a = q ∧ b = s ∧ c = p ∧ d = r) ∨ (a = q ∧ b = s ∧ c = r ∧ d = p) ∨
    (a = r ∧ b = p ∧ c = q ∧ d = s) ∨ (a = r ∧ b = p ∧ c = s ∧ d = q) ∨
    (a = r ∧ b = q ∧ c = p ∧ d = s) ∨ (a = r ∧ b = q ∧ c = s ∧ d = p) ∨
    (a = r ∧ b = s ∧ c = p ∧ d = q) ∨ (a = r ∧ b = s ∧ c = q ∧ d = p) ∨
    (a = s ∧ b = p ∧ c = q ∧ d = r) ∨ (a = s ∧ b = p ∧ c = r ∧ d = q) ∨
    (a = s ∧ b = q ∧ c = p ∧ d = r) ∨ (a = s ∧ b = q ∧ c = r ∧ d = p) ∧
    a * b - c * d ≥ 2 := by

  have h2 : p * q + p * r + p * s + q * r + q * s + r * s = 30 := by
    have h3 : (p + q + r + s) ^ 2 = p^2 + q^2 + r^2 + s^2 + 2 * (p * q + p * r + p * s + q * r + q * s + r * s) := by 
      ring
    rw [h₀, h₁] at h3
    linarith
  use p, s, q, r 
  simp at *
  all_goals
  nlinarith [sq_nonneg (p - s + q - r), sq_nonneg (p + s - (q + r)), sq_nonneg (p - r + q - s), sq_nonneg (p - q + r - s), sq_nonneg (p * s - q * r)]