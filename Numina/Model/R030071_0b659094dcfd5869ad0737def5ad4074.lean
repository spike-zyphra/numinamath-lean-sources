import Mathlib

theorem inequalities_230207 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    2 ≤ 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) + 1 / (a + 4 * c + 3 * d) +
        1 / (4 * b + 3 * c + d) := by 
  have h2 : 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) + 1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) - 2 ≥ 0 := by
    have pos1 : 0 < (4 * a + 3 * b + c) * (3 * a + b + 4 * d) * (a + 4 * c + 3 * d) * (4 * b + 3 * c + d) := by positivity
    have h3 : 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) + 1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) - 2 =
        ( (3 * a + b + 4 * d) * (a + 4 * c + 3 * d) * (4 * b + 3 * c + d) + (4 * a + 3 * b + c) * (a + 4 * c + 3 * d) * (4 * b + 3 * c + d) + (4 * a + 3 * b + c) * (3 * a + b + 4 * d) * (4 * b + 3 * c + d) + (4 * a + 3 * b + c) * (3 * a + b + 4 * d) * (a + 4 * c + 3 * d) - 2 * (4 * a + 3 * b + c) * (3 * a + b + 4 * d) * (a + 4 * c + 3 * d) * (4 * b + 3 * c + d) ) / ( (4 * a + 3 * b + c) * (3 * a + b + 4 * d) * (a + 4 * c + 3 * d) * (4 * b + 3 * c + d) ) := by 
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    -- Show numerator is >= 0
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a + b - c - d), sq_nonneg (a + d - b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]
    positivity
  linarith