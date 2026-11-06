import Mathlib

theorem inequalities_250453 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    a / (a ^ 3 + 5) + b / (b ^ 3 + 5) + c / (c ^ 3 + 5) + d / (d ^ 3 + 5) ≤ 2 / 3 := by

  have h1 : a / (a ^ 3 + 5) ≤ (a + 1) / 12 := by 
    have h10 : 0 < a ^ 3 + 5 := by
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a), sq_nonneg (a - 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a ^ 2 - 4), sq_nonneg (a * (a - 1)), sq_nonneg ((a + 1) * (a - 1)), mul_pos ha (show 0 < a by linarith), pow_two_nonneg (a - 1), pow_two_nonneg (a + 1)]

  have h2 : b / (b ^ 3 + 5) ≤ (b + 1) / 12 := by
    have h20 : 0 < b ^ 3 + 5 := by
      nlinarith [sq_nonneg (b ^ 2), sq_nonneg (b), sq_nonneg (b - 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b ^ 2 - 1), sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (b ^ 2 - 4), sq_nonneg (b * (b - 1)), sq_nonneg ((b + 1) * (b - 1)), mul_pos hb (show 0 < b by linarith), pow_two_nonneg (b - 1), pow_two_nonneg (b + 1)]

  have h3 : c / (c ^ 3 + 5) ≤ (c + 1) / 12 := by 
    have h30 : 0 < c ^ 3 + 5 := by
      nlinarith [sq_nonneg (c ^ 2), sq_nonneg (c), sq_nonneg (c - 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (c ^ 2 - 4), sq_nonneg (c * (c - 1)), sq_nonneg ((c + 1) * (c - 1)), mul_pos hc (show 0 < c by linarith), pow_two_nonneg (c - 1), pow_two_nonneg (c + 1)]

  have h4 : d / (d ^ 3 + 5) ≤ (d + 1) / 12 := by 
    have h40 : 0 < d ^ 3 + 5 := by
      nlinarith [sq_nonneg (d ^ 2), sq_nonneg (d), sq_nonneg (d - 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (d ^ 2 - 1), sq_nonneg (d - 1), sq_nonneg (d + 1), sq_nonneg (d ^ 2 - 4), sq_nonneg (d * (d - 1)), sq_nonneg ((d + 1) * (d - 1)), mul_pos hd (show 0 < d by linarith), pow_two_nonneg (d - 1), pow_two_nonneg (d + 1)]

  have h5 : a / (a ^ 3 + 5) + b / (b ^ 3 + 5) + c / (c ^ 3 + 5) + d / (d ^ 3 + 5) ≤ (a + 1) / 12 + (b + 1) / 12 + (c + 1) / 12 + (d + 1) / 12 := by
    linarith [h1, h2, h3, h4]

  have h6 : (a + 1) / 12 + (b + 1) / 12 + (c + 1) / 12 + (d + 1) / 12 = 2 / 3 := by 
    have h7 : a + b + c + d = 4 := h
    linarith

  linarith [h5, h6]