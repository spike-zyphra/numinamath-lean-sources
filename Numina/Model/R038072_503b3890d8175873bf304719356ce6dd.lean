import Mathlib

theorem inequalities_91161 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b / (c * d) = (a + b) / (c + d)) : (a + b) * (c + d) ≥ (a + c) * (b + d) := by 
  have h1 : 0 < c * d := by
    apply mul_pos
    exact hc
    exact hd
  have h2 : 0 < c + d := by
    nlinarith
  have h3 : a * b * (c + d) = c * d * (a + b) := by 
    have h4 : c * d ≠ 0 := by
      nlinarith
    have h5 : c + d ≠ 0 := by
      nlinarith
    field_simp [h4, h5] at h ⊢
    linarith
  have h4 : a * c + b * d ≥ a * b + c * d := by 
    have h5 : a * b * (c + d) = c * d * (a + b) := h3
    nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), sq_nonneg (a - d), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith)]
  have h5 : (a + b) * (c + d) ≥ (a + c) * (b + d) := by
    nlinarith [h4]
  linarith