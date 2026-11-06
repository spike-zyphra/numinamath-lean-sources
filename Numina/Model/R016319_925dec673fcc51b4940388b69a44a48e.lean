import Mathlib

open Real

theorem inequalities_252924 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) :
    (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * (b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1) ≥
    4 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) := by

  have h1 : a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = (a ^ 3 + 1) * (a ^ 2 + a + 1) := by
    ring
  have h2 : b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1 = (b ^ 3 + 1) * (b ^ 2 + b + 1) := by
    ring

  rw [h1, h2]

  have h3 : 0 < a ^ 2 + a + 1 := by
    nlinarith [sq_nonneg (a + 1 / 2), sq_pos_of_pos ha]
  have h4 : 0 < b ^ 2 + b + 1 := by
    nlinarith [sq_nonneg (b + 1 / 2), sq_pos_of_pos hb]

  have h5 : (a ^ 3 + 1) * (b ^ 3 + 1) ≥ 4 := by
    have h6 : a ^ 3 + b ^ 3 ≥ 2 := by
      have h7 : a ^ 3 * b ^ 3 = 1 := by
        calc
          a ^ 3 * b ^ 3 = (a * b) ^ 3 := by ring
          _ = (1) ^ 3 := by rw [hab]
          _ = (1 : ℝ) := by norm_num
      nlinarith [sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a - b), sq_nonneg (a * b - 1), mul_pos ha hb, sq_nonneg (a ^ 3 * b ^ 3 - 1)]
    nlinarith [sq_nonneg (a ^ 3 * b ^ 3 - 1), h6, sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a - b), sq_nonneg (a * b - 1), mul_pos ha hb]

  have h7 : (a ^ 3 + 1) * (b ^ 3 + 1) * ((a ^ 2 + a + 1) * (b ^ 2 + b + 1)) ≥ 4 * ((a ^ 2 + a + 1) * (b ^ 2 + b + 1)) := by
    have h8 : (a ^ 3 + 1) * (b ^ 3 + 1) ≥ 4 := h5
    have h9 : 0 < (a ^ 2 + a + 1) * (b ^ 2 + b + 1) := mul_pos h3 h4
    nlinarith [h8, h9]

  linarith