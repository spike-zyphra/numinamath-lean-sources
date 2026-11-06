import Mathlib

theorem inequalities_288079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
     (2 * b + a + c)^2 / (2 * b^2 + (c + a)^2) +
     (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2)) ≤ 8 := by

  have h2 : 0 < 2 * a^2 + (b + c)^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h3 : 0 < 2 * b^2 + (c + a)^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h4 : 0 < 2 * c^2 + (a + b)^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h6 : ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + a + c)^2 / (2 * b^2 + (c + a)^2) + (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2)) - 8 ≤ 0 := by

    have h7 : ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + a + c)^2 / (2 * b^2 + (c + a)^2) + (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2)) - 8 =
              ((2 * a + b + c) ^ 2 * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2) +
               (2 * b + a + c) ^ 2 * (2 * a^2 + (b + c)^2) * (2 * c^2 + (a + b)^2) +
               (2 * c + a + b) ^ 2 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) - 8 * ( (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2) )) / ((2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) := by
      field_simp
      ring

    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show Numerator is Nonpositive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos ha (show 0 < a * b by nlinarith), mul_pos ha (show 0 < a * c by nlinarith), mul_pos hb (show 0 < b * c by nlinarith), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
    · -- Show Denominator is Nonnegative
      positivity

  linarith [h6]