import Mathlib

theorem inequalities_250141 (a b c d : ℝ) (ha : 0 < a) (hle : a ≤ b ∧ b ≤ c ∧ c ≤ d)
    (hsum : a + b + c + d = 1) :
    a^2 + 3 * b^2 + 5 * c^2 + 7 * d^2 ≥ 1 := by
  nlinarith [sq_nonneg (a - 1/4), sq_nonneg (b - 1/4), sq_nonneg (c - 1/4), sq_nonneg (d - 1/4), 
          hle.1, hle.2.1, hle.2.2, hsum, mul_pos ha (show (0 : ℝ) < a by linarith)]