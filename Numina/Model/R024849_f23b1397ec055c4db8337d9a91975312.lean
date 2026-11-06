import Mathlib

theorem inequalities_597368 (a b c d p q : ℝ)
    (h₀ : a * b + c * d = 2 * p * q)
    (h₁ : a * c ≥ p ^ 2)
    (h₂ : p ^ 2 > 0) :
    b * d ≤ q ^ 2 := by

  have h3 : (a * b + c * d) ^ 2 ≥ 4 * (a * c) * (b * d) := by
    nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a * b - c * d), sq_nonneg (a * d + b * c), sq_nonneg (a * c - b * d)]

  have h4 : (a * b + c * d) ^ 2 = 4 * (p * q) ^ 2 := by
    calc
      (a * b + c * d) ^ 2 = (2 * p * q) ^ 2 := by rw [h₀]
      _ = 4 * (p * q) ^ 2 := by ring

  have h5 : 4 * (p * q) ^ 2 ≥ 4 * (a * c) * (b * d) := by
    nlinarith [h3, h4]

  have h6 : (p * q) ^ 2 ≥ (a * c) * (b * d) := by
    nlinarith

  have h7 : (p * q) ^ 2 ≥ p ^ 2 * (b * d) := by
    nlinarith [h6, h₁]

  have h8 : q ^ 2 ≥ b * d := by
    have hp : p ^ 2 > 0 := h₂
    have h9 : p ^ 2 * q ^ 2 ≥ p ^ 2 * (b * d) := by
      nlinarith [h7]
    have h10 : q ^ 2 ≥ b * d := by
      nlinarith [h9, hp]
    linarith

  linarith [h8]