import Mathlib

theorem algebra_241525 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
(a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) ≥ 4:= by
  have h1 : a + b > 0 := by nlinarith
  have h2 : b + c > 0 := by nlinarith
  have h3 : c + d > 0 := by nlinarith
  have h4 : d + a > 0 := by nlinarith
  have h5 : (a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) - 4 ≥ 0 := by
    have pos1 : a + b > 0 := h1
    have pos2 : b + c > 0 := h2
    have pos3 : c + d > 0 := h3
    have pos4 : d + a > 0 := h4
    have h6 : (a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) - 4 =
        ((a + c) * (b + c) * (c + d) * (d + a) + 
        (b + d) * (a + b) * (c + d) * (d + a) + 
        (c + a) * (a + b) * (b + c) * (d + a) + 
        (d + b) * (a + b) * (b + c) * (c + d) - 4 * (a + b) * (b + c) * (c + d) * (d + a)) / ((a + b) * (b + c) * (c + d) * (d + a)) := by 
      field_simp
      ring
    rw [h6]
    have pos7 : (a + b) * (b + c) * (c + d) * (d + a) > 0 := by positivity
    have h7 : ((a + c) * (b + c) * (c + d) * (d + a) + 
        (b + d) * (a + b) * (c + d) * (d + a) + 
        (c + a) * (a + b) * (b + c) * (d + a) + 
        (d + b) * (a + b) * (b + c) * (c + d) - 4 * (a + b) * (b + c) * (c + d) * (d + a)) ≥ 0 := by
      nlinarith [ 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
        sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
        sq_nonneg (a + b - c - d), sq_nonneg (a + d - b - c), 
        sq_nonneg (a * b - c * d), sq_nonneg (b * c - a * d), 
        sq_nonneg (a - b + c - d), sq_nonneg (a - d + b - c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
        mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
        mul_pos (show 0 < a + b by linarith) (show 0 < a + c by linarith), 
        mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith), 
        mul_pos (show 0 < b + c by linarith) (show 0 < c + d by linarith), 
        mul_pos (show 0 < c + d by linarith) (show 0 < d + a by linarith), 
        mul_pos (show 0 < a + b by linarith) (show 0 < c + d by linarith), 
        mul_pos (show 0 < a + c by linarith) (show 0 < b + d by linarith)
      ]
    apply div_nonneg
    linarith
    all_goals linarith
  linarith