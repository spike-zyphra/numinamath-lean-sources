import Mathlib

theorem inequalities_33322 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 < b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) +
        a / (d * a + a + 1) ∧
    b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) +
        a / (d * a + a + 1) < 2 := by
  have ha1 : 0 < a * b + b + 1 := by positivity
  have hb1 : 0 < b * c + c + 1 := by positivity
  have hc1 : 0 < c * d + d + 1 := by positivity
  have hd1 : 0 < d * a + a + 1 := by positivity
  constructor
  · -- Prove the left side (i.e., 1 < S)
    have h1 : 1 < b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) + a / (d * a + a + 1) := by
      have h4 : b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) + a / (d * a + a + 1) - 1 > 0 := by
        have h10 : b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) + a / (d * a + a + 1) - 1 =
            (b * (b * c + c + 1) * (c * d + d + 1) * (d * a + a + 1) +
             c * (a * b + b + 1) * (c * d + d + 1) * (d * a + a + 1) +
             d * (a * b + b + 1) * (b * c + c + 1) * (d * a + a + 1) +
             a * (a * b + b + 1) * (b * c + c + 1) * (c * d + d + 1) - (a * b + b + 1) * (b * c + c + 1) * (c * d + d + 1) * (d * a + a + 1)) / ((a * b + b + 1) * (b * c + c + 1) * (c * d + d + 1) * (d * a + a + 1)) := by
          field_simp
          ring
        rw [h10] at *
        apply div_pos
        ·
          nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * d - 1), sq_nonneg (d * a - 1),
          sq_nonneg (a - c), sq_nonneg (b - d),
          sq_nonneg (a * b * c - 1), sq_nonneg (b * c * d - 1), sq_nonneg (c * d * a - 1), sq_nonneg (d * a * b - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha (show (0 : ℝ) < d by positivity), mul_pos hb hc, mul_pos hb (show (0 : ℝ) < d by positivity), mul_pos hc (show (0 : ℝ) < d by positivity), mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos ha hb) (show (0 : ℝ) < d by positivity), mul_pos (mul_pos ha hc) (show (0 : ℝ) < d by positivity), mul_pos (mul_pos hb hc) (show (0 : ℝ) < d by positivity)]
        all_goals positivity
      linarith
    linarith
  · -- Prove the right side (i.e., 1 < S)
    have h2 : b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) + a / (d * a + a + 1) < 2 := by
      have h32 : 0 < 2 - (b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) + a / (d * a + a + 1)) := by
        have h10 : 2 - (b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) + a / (d * a + a + 1)) =
            (2 * (a * b + b + 1) * (b * c + c + 1) * (c * d + d + 1) * (d * a + a + 1) - (b * (b * c + c + 1) * (c * d + d + 1) * (d * a + a + 1) + c * (a * b + b + 1) * (c * d + d + 1) * (d * a + a + 1) + d * (a * b + b + 1) * (b * c + c + 1) * (d * a + a + 1) + a * (a * b + b + 1) * (b * c + c + 1) * (c * d + d + 1))) / ((a * b + b + 1) * (b * c + c + 1) * (c * d + d + 1) * (d * a + a + 1)) := by
          field_simp
          ring
        rw [h10] at *
        apply div_pos
        ·
          nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * d - 1), sq_nonneg (d * a - 1),
          sq_nonneg (a - c), sq_nonneg (b - d),
          sq_nonneg (a * b * c - 1), sq_nonneg (b * c * d - 1), sq_nonneg (c * d * a - 1), sq_nonneg (d * a * b - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha (show (0 : ℝ) < d by positivity), mul_pos hb hc, mul_pos hb (show (0 : ℝ) < d by positivity), mul_pos hc (show (0 : ℝ) < d by positivity), mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos ha hb) (show (0 : ℝ) < d by positivity), mul_pos (mul_pos ha hc) (show (0 : ℝ) < d by positivity), mul_pos (mul_pos hb hc) (show (0 : ℝ) < d by positivity)]
        all_goals positivity
      linarith
    linarith