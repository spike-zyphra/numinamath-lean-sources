import Mathlib

theorem inequalities_89649 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    a / (a ^ 3 + 4) + b / (b ^ 3 + 4) + c / (c ^ 3 + 4) +
    d / (d ^ 3 + 4) ≤ 4 / 5 := by 
  have h1 : a / (a ^ 3 + 4) ≤ (2 * a + 3) / 25 := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 2), 
      sq_nonneg (a * (a - 1)), sq_nonneg ((a - 1) * a), sq_nonneg ((a - 2) * (a - 1)), 
      sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 2), a, mul_pos ha (show 0 < a^2 by nlinarith)]
  have h2 : b / (b ^ 3 + 4) ≤ (2 * b + 3) / 25 := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (b - 2), 
      sq_nonneg (b * (b - 1)), sq_nonneg ((b - 1) * b), sq_nonneg ((b - 2) * (b - 1)), 
      sq_nonneg (b ^ 2 - 1), sq_nonneg (b - 1), sq_nonneg (b ^ 2 - 2), b, mul_pos hb (show 0 < b^2 by nlinarith)]
  have h3 : c / (c ^ 3 + 4) ≤ (2 * c + 3) / 25 := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 2), 
      sq_nonneg (c * (c - 1)), sq_nonneg ((c - 1) * c), sq_nonneg ((c - 2) * (c - 1)), 
      sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1), sq_nonneg (c ^ 2 - 2), c, mul_pos hc (show 0 < c^2 by nlinarith)]
  have h4 : d / (d ^ 3 + 4) ≤ (2 * d + 3) / 25 := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (d - 1), sq_nonneg (d ^ 2 - 1), sq_nonneg (d - 2), 
      sq_nonneg (d * (d - 1)), sq_nonneg ((d - 1) * d), sq_nonneg ((d - 2) * (d - 1)), 
      sq_nonneg (d ^ 2 - 1), sq_nonneg (d - 1), sq_nonneg (d ^ 2 - 2), d, mul_pos hd (show 0 < d^2 by nlinarith)]
  have h5 : a / (a ^ 3 + 4) + b / (b ^ 3 + 4) + c / (c ^ 3 + 4) + d / (d ^ 3 + 4) ≤ (2 * a + 3) / 25 + (2 * b + 3) / 25 + (2 * c + 3) / 25 + (2 * d + 3) / 25 := by 
    linarith [h1, h2, h3, h4]
  have h6 : (2 * a + 3) / 25 + (2 * b + 3) / 25 + (2 * c + 3) / 25 + (2 * d + 3) / 25 = 4 / 5 := by 
    have h7 : a + b + c + d = 4 := h 
    linarith 
  linarith [h5, h6]