import Mathlib

theorem algebra_240720 {a b c d : ℝ} (h : a ^ 2 + b ^ 2 + (a + b) ^ 2 = c ^ 2 + d ^ 2 + (c + d) ^ 2) :
    a ^ 4 + b ^ 4 + (a + b) ^ 4 = c ^ 4 + d ^ 4 + (c + d) ^ 4 := by
  have h1 : a ^ 2 + b ^ 2 + a * b = c ^ 2 + d ^ 2 + c * d := by
    nlinarith [h]
  have h2 : a ^ 4 + b ^ 4 + (a + b) ^ 4 = 2 * (a ^ 2 + b ^ 2 + a * b) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b)]
  have h3 : c ^ 4 + d ^ 4 + (c + d) ^ 4 = 2 * (c ^ 2 + d ^ 2 + c * d) ^ 2 := by
    nlinarith [sq_nonneg (c ^ 2 - d ^ 2), sq_nonneg (c - d), sq_nonneg (c + d)]
  calc
    a ^ 4 + b ^ 4 + (a + b) ^ 4 = 2 * (a ^ 2 + b ^ 2 + a * b) ^ 2 := by linarith [h2]
    _ = 2 * (c ^ 2 + d ^ 2 + c * d) ^ 2 := by
      rw [h1]
    _ = c ^ 4 + d ^ 4 + (c + d) ^ 4 := by linarith [h3]