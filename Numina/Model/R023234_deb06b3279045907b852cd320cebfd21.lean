import Mathlib

theorem number_theory_181032 (a b c : ℕ) (h₀ : 0 < a) (h₁ : a ≤ b) (h₂ : b < c)
    (h₃ : a^2 + b^2 = c^2) : a ≠ 1 := by 
  by_contra h
  rw [show a = 1 by linarith] at h₃
  have h₄ : 1 ≤ b := by 
    have h₅ : a ≤ b := h₁
    rw [show a = 1 by linarith] at h₅
    linarith
  have h₆ : c > b := by linarith
  have h₇ : c ≥ b + 1 := by 
    omega
  have h₈ : c ^ 2 ≥ (b + 1) ^ 2 := by
    apply Nat.pow_le_pow_of_le_left
    linarith
  have h₉ : 1 + b ^ 2 ≥ (b + 1) ^ 2 := by
    nlinarith [h₃, h₈]
  have h₁₀ : b ≤ 0 := by
    nlinarith
  have h₁₁ : b = 0 := by
    omega
  omega