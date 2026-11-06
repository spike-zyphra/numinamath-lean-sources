import Mathlib

theorem inequalities_108245 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    (b * c * d / (1 - a) ^ 2 + c * d * a / (1 - b) ^ 2 + d * a * b / (1 - c) ^ 2 +
     a * b * c / (1 - d) ^ 2) ≤ 1 / 9 := by

  have h1 : 1 - a = b + c + d := by linarith
  have h2 : 1 - b = a + c + d := by linarith
  have h3 : 1 - c = a + b + d := by linarith
  have h4 : 1 - d = a + b + c := by linarith

  have h5 : b * c * d / (1 - a) ^ 2 ≤ (b + c + d) / 27 := by
    rw [h1]
    have h6 : 0 < b + c + d := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < d by linarith)]

  have h6 : c * d * a / (1 - b) ^ 2 ≤ (a + c + d) / 27 := by 
    rw [h2]
    have h7 : 0 < a + c + d := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (c - d), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
      mul_pos (show 0 < a * c by nlinarith) (show 0 < d by linarith)]

  have h7 : d * a * b / (1 - c) ^ 2 ≤ (a + b + d) / 27 := by 
    rw [h3]
    have h8 : 0 < a + b + d := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - d), sq_nonneg (b - d), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < d by linarith)]

  have h8 : a * b * c / (1 - d) ^ 2 ≤ (a + b + c) / 27 := by 
    rw [h4]
    have h9 : 0 < a + b + c := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)]

  have h9 : b * c * d / (1 - a) ^ 2 + c * d * a / (1 - b) ^ 2 + d * a * b / (1 - c) ^ 2 + a * b * c / (1 - d) ^ 2 ≤ (b + c + d) / 27 + (a + c + d) / 27 + (a + b + d) / 27 + (a + b + c) / 27 := by
    linarith [h5, h6, h7, h8]

  have h10 : (b + c + d) / 27 + (a + c + d) / 27 + (a + b + d) / 27 + (a + b + c) / 27 = 1 / 9 := by
    field_simp at *
    nlinarith [h]
  linarith [h9, h10]