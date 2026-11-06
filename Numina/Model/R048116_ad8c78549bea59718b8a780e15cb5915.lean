import Mathlib

theorem inequalities_63714 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    4 ≤ (a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < a * d := mul_pos ha hd
  have h4 : 0 < b * c := mul_pos hb hc
  have h5 : 0 < b * d := mul_pos hb hd
  have h6 : 0 < c * d := mul_pos hc hd

  have h7 : 0 < (a + b) * (b + c) * (c + d) * (d + a) := by
    positivity
  have h8 : (a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) - 4 ≥ 0 := by
    have h9 : 0 < (a + b) * (b + c) * (c + d) * (d + a) := by positivity
    have h10 : (a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) - 4 =
        ( (a + c) * (b + c) * (c + d) * (d + a) + (b + d) * (a + b) * (c + d) * (d + a) + (c + a) * (a + b) * (b + c) * (d + a) + (d + b) * (a + b) * (b + c) * (c + d) - 4 * (a + b) * (b + c) * (c + d) * (d + a) ) / ( (a + b) * (b + c) * (c + d) * (d + a) ) := by
      field_simp
      ring
    rw [h10] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
              sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
              sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), 
              mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, 
              mul_pos hc hd, 
              mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith), 
              mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith) 
            ]
    all_goals positivity
  linarith