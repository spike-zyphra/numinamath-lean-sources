import Mathlib

theorem inequalities_598253 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    2 ≤ a / (1 + b ^ 2) + b / (1 + c ^ 2) + c / (1 + d ^ 2) + d / (1 + a ^ 2) := by

  have h3 : a / (1 + b ^ 2) ≥ a - a * b / 2 := by
    have h3 : 0 < 1 + b ^ 2 := by
      nlinarith [sq_pos_of_pos hb]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]

  have h4 : b / (1 + c ^ 2) ≥ b - b * c / 2 := by
    have h4 : 0 < 1 + c ^ 2 := by
      nlinarith [sq_pos_of_pos hc]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1), sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos hb hc]

  have h5 : c / (1 + d ^ 2) ≥ c - c * d / 2 := by
    have h5 : 0 < 1 + d ^ 2 := by
      nlinarith [sq_pos_of_pos hd]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (d - 1), sq_pos_of_pos hc, sq_pos_of_pos hd, mul_pos hc hd]

  have h6 : d / (1 + a ^ 2) ≥ d - d * a / 2 := by
    have h6 : 0 < 1 + a ^ 2 := by
      nlinarith [sq_pos_of_pos ha]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_pos_of_pos ha, sq_pos_of_pos hd, mul_pos ha hd]

  have h7 : a / (1 + b ^ 2) + b / (1 + c ^ 2) + c / (1 + d ^ 2) + d / (1 + a ^ 2) ≥ (a + b + c + d) - (a * b + b * c + c * d + d * a) / 2 := by
    linarith [h3, h4, h5, h6]

  have h8 : a * b + b * c + c * d + d * a ≤ 4 := by
    have h10 : a + b + c + d = 4 := h
    nlinarith [sq_nonneg (a + c - 2), sq_nonneg (b + d - 2), sq_nonneg (a + c - (b + d)), mul_pos ha hb, mul_pos hb hc, mul_pos hc hd, mul_pos ha hc, mul_pos hb hd, mul_pos ha hd, mul_pos hc ha]

  have h9 : (a + b + c + d) - (a * b + b * c + c * d + d * a) / 2 ≥ 2 := by
    have h10 : a + b + c + d = 4 := h
    nlinarith [h8]

  linarith [h7, h9]