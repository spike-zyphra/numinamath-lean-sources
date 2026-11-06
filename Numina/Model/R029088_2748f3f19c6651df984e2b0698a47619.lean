import Mathlib

theorem algebra_228260 {a b c d : ℝ} (h : a^2 + d^2 - 2 * (a * b + b * c + c * d - b^2 - c^2) = 0) :
    a = b ∧ b = c ∧ c = d := by
  have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 = 0 := by 
    ring_nf at h ⊢
    linarith
  have h2 : (a - b) ^ 2 = 0 := by 
    linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d)]
  have h3 : a - b = 0 := by 
    nlinarith
  have h4 : (b - c) ^ 2 = 0 := by 
    linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d)]
  have h5 : b - c = 0 := by 
    nlinarith
  have h6 : (c - d) ^ 2 = 0 := by 
    linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d)]
  have h7 : c - d = 0 := by 
    nlinarith
  constructor
  · -- a = b
    linarith
  constructor
  · -- b = c
    linarith
  · -- c = d
    linarith