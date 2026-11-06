import Mathlib

theorem inequalities_1923 (a : ℝ) (ha : a > 0) :
  2 * (a ^ 4 + (a + 2) ^ 6 + (a + 4) ^ 8 + (a + 6) ^ 10) ≥ (a ^ 2 + (a + 2) ^ 3 + (a + 4) ^ 4 + (a + 6) ^ 5) ^ 2 := by
  nlinarith [sq_nonneg (a ^ 2 - (a + 2) ^ 3), sq_nonneg (a ^ 2 - (a + 4) ^ 4), sq_nonneg (a ^ 2 - (a + 6) ^ 5),
          sq_nonneg ((a + 2) ^ 3 - (a + 4) ^ 4), sq_nonneg ((a + 2) ^ 3 - (a + 6) ^ 5), sq_nonneg ((a + 4) ^ 4 - (a + 6) ^ 5),
          sq_nonneg (a ^ 2 - (a + 2) ^ 3 + (a + 4) ^ 4 - (a + 6) ^ 5), sq_nonneg (a ^ 2 - (a + 4) ^ 4 + (a + 2) ^ 3 - (a + 6) ^ 5),
          sq_nonneg (a ^ 2 - (a + 6) ^ 5 + (a + 2) ^ 3 - (a + 4) ^ 4), sq_nonneg ((a + 2) ^ 3 - (a + 4) ^ 4 + (a + 6) ^ 5 - a ^ 2),
          sq_nonneg ((a ^ 2 - (a + 2) ^ 3) + ((a + 4) ^ 4 - (a + 6) ^ 5)), sq_nonneg ((a ^ 2 - (a + 6) ^ 5) + ((a + 2) ^ 3 - (a + 4) ^ 4)), sq_nonneg ((a + 2) ^ 3 - a ^ 2), sq_nonneg ((a + 4) ^ 4 - (a + 2) ^ 3), sq_nonneg ((a + 6) ^ 5 - (a + 4) ^ 4), mul_pos ha (show 0 < a from by linarith), sq_nonneg (a + 1), sq_nonneg (a + 3), sq_nonneg (a + 5)]