import Mathlib

open Real

theorem inequalities_318187 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    4 / 3 ≤ a / (b + c + d) + b / (c + d + a) + c / (d + a + b) +
    d / (a + b + c) := by
  have pos1 : 0 < (b + c + d) := by linarith
  have pos2 : 0 < (c + d + a) := by linarith
  have pos3 : 0 < (d + a + b) := by linarith
  have pos4 : 0 < (a + b + c) := by linarith
  have h5 : a / (b + c + d) + b / (c + d + a) + c / (d + a + b) + d / (a + b + c) - 4 / 3 ≥ 0 := by
    have h6 : a / (b + c + d) + b / (c + d + a) + c / (d + a + b) + d / (a + b + c) - 4 / 3 =
        (a * (c + d + a) * (d + a + b) * (a + b + c) +
         b * (b + c + d) * (d + a + b) * (a + b + c) +
         c * (b + c + d) * (c + d + a) * (a + b + c) +
         d * (b + c + d) * (c + d + a) * (d + a + b) - 4 / 3 * (b + c + d) * (c + d + a) * (d + a + b) * (a + b + c)) / ((b + c + d) * (c + d + a) * (d + a + b) * (a + b + c)) := by
      field_simp
      ring
    rw [h6] at *
    have pos1 : 0 < (b + c + d) * (c + d + a) * (d + a + b) * (a + b + c) := by positivity
    have h7 : a * (c + d + a) * (d + a + b) * (a + b + c) +
         b * (b + c + d) * (d + a + b) * (a + b + c) +
         c * (b + c + d) * (c + d + a) * (a + b + c) +
         d * (b + c + d) * (c + d + a) * (d + a + b) - 4 / 3 * (b + c + d) * (c + d + a) * (d + a + b) * (a + b + c) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
        sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
        mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
      ]
    apply div_nonneg h7 (by positivity)
  linarith