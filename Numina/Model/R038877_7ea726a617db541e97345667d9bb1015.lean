import Mathlib
open Real

theorem inequalities_605868 {a b c : ℝ}
    (h_apos : 0 < a)
    (h_bpos : 0 < b)
    (h_cpos : 0 < c)
    (h : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 = 3) :
    (a ^ 2 - a + 1) * (b ^ 2 - b + 1) * (c ^ 2 - c + 1) ≥ 1 := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a * (b - 1)), sq_nonneg (b * (c - 1)), sq_nonneg (c * (a - 1)),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos h_apos h_bpos, mul_pos h_bpos h_cpos, mul_pos h_cpos h_apos,
          mul_pos (mul_pos h_apos h_bpos) h_cpos]