import Mathlib

theorem inequalities_63729 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a / b + b / c + c / d + d / a = 6) (h2 : b / a + c / b + d / c + a / d = 36) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 > a * b + a * c + a * d + b * c + b * d + c * d := by 
  have h3 : 0 < a * b * c * d := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    all_goals
      linarith
  have eq1 : a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c = 6 * (a * b * c * d) := by
    have h4 : a / b + b / c + c / d + d / a = 6 := h1
    have h5 : b ≠ 0 := by linarith
    have h6 : c ≠ 0 := by linarith
    have h7 : d ≠ 0 := by linarith
    have h8 : a ≠ 0 := by linarith
    field_simp [h5, h6, h7, h8] at h4 ⊢
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]

  have eq2 : b ^ 2 * c * d + c ^ 2 * a * d + d ^ 2 * a * b + a ^ 2 * b * c = 36 * (a * b * c * d) := by
    have h9 : b / a + c / b + d / c + a / d = 36 := h2
    have h5 : a ≠ 0 := by linarith
    have h6 : b ≠ 0 := by linarith
    have h7 : c ≠ 0 := by linarith
    have h8 : d ≠ 0 := by linarith
    field_simp [h5, h6, h7, h8] at h9 ⊢
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
    mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
    mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * d from mul_pos hc hd),
    mul_pos (show 0 < a * c from mul_pos ha hc) (show 0 < b * d from mul_pos hb hd)
  ]