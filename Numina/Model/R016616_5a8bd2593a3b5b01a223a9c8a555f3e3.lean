import Mathlib

theorem inequalities_602186 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
  have h1 : 0 < a * b * c * d := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < a + b + c + d := by
    nlinarith
  have h3 : 1 / a + 1 / b + 4 / c + 16 / d - 64 / (a + b + c + d) ≥ 0 := by 
    have h4 : 0 < a * b * c * d * (a + b + c + d) := by
      positivity
    have h5 : (1 / a + 1 / b + 4 / c + 16 / d - 64 / (a + b + c + d)) =
        ( (b * c * d * (a + b + c + d) + a * c * d * (a + b + c + d) + 4 * a * b * d * (a + b + c + d) + 16 * a * b * c * (a + b + c + d) - 64 * (a * b * c * d) ) / (a * b * c * d * (a + b + c + d)) ) := by
      field_simp
      <;> ring
    rw [h5] at *
    apply div_nonneg
    · -- To complete the proof, we can apply `nlinarith` with several positivity facts
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 2), sq_nonneg (a - d / 4), sq_nonneg (b - c / 2), sq_nonneg (b - d / 4), sq_nonneg (c / 2 - d / 4),
                sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c),
                mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
                mul_pos hb hc, mul_pos hb hd, 
                mul_pos hc hd]
    · -- Denominator is clearly positive
      positivity
  linarith