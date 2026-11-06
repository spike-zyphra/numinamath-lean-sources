import Mathlib

theorem Inequalities_102070 (a b c d m : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hm : 0 < m) (h : a + b + c + d + m = 1):
    1 / a + 1 / b + 1 / c + 1 / d + 1 / m ≥ 25:= by
  have h1 : 1 / a + 1 / b + 1 / c + 1 / d + 1 / m - 25 ≥ 0 := by
    have h2 : 0 < a * b * c * d * m := by
      apply mul_pos
      apply mul_pos
      apply mul_pos
      apply mul_pos
      all_goals
        positivity
    have h3 : (1 / a + 1 / b + 1 / c + 1 / d + 1 / m - 25) = ( (b * c * d * m + a * c * d * m + a * b * d * m + a * b * c * m + a * b * c * d - 25 * a * b * c * d * m) ) / (a * b * c * d * m) := by 
      field_simp
      ring
    rw [h3] 
    have h4 : b * c * d * m + a * c * d * m + a * b * d * m + a * b * c * m + a * b * c * d - 25 * a * b * c * d * m ≥ 0 := by
      have h5 : a + b + c + d + m = 1 := h
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - m),
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - m),
          sq_nonneg (c - d), sq_nonneg (c - m),
          sq_nonneg (d - m),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha hm,
          mul_pos hb hc, mul_pos hb hd, mul_pos hb hm,
          mul_pos hc hd, mul_pos hc hm, mul_pos hd hm,
          mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos ha hb) hd, mul_pos (mul_pos ha hb) hm,
          mul_pos (mul_pos ha hc) hb, mul_pos (mul_pos ha hc) hd, mul_pos (mul_pos ha hc) hm,
          mul_pos (mul_pos ha hd) hb, mul_pos (mul_pos ha hd) hc, mul_pos (mul_pos ha hd) hm,
          mul_pos (mul_pos hb hc) ha, mul_pos (mul_pos hb hc) hd, mul_pos (mul_pos hb hc) hm,
          mul_pos (mul_pos hb hd) ha, mul_pos (mul_pos hb hd) hc, mul_pos (mul_pos hb hd) hm,
          mul_pos (mul_pos hc hd) ha, mul_pos (mul_pos hc hd) hb, mul_pos (mul_pos hc hd) hm]
    have h7 : (b * c * d * m + a * c * d * m + a * b * d * m + a * b * c * m + a * b * c * d - 25 * a * b * c * d * m) / (a * b * c * d * m) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith