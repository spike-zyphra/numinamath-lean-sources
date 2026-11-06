import Mathlib

theorem algebra_308897 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a > b) :
    a^2 + 1 / (b * (a - b)) ≥ 4 := by 
  have h1 : b * (a - b) > 0 := by
    apply mul_pos
    all_goals linarith
  have h2 : a^2 + 1 / (b * (a - b)) - 4 ≥ 0 := by
    have h3 : a^2 + 1 / (b * (a - b)) - 4 =
        (a^2 * (b * (a - b)) + 1 - 4 * (b * (a - b))) / (b * (a - b)) := by
      field_simp [(show b * (a - b) ≠ 0 by positivity)]
      ring
    rw [h3] 
    have h4 : a^2 * (b * (a - b)) + 1 - 4 * (b * (a - b)) ≥ 0 := by
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - (a - b)), sq_nonneg (a^2 - 2), sq_nonneg (b * (a - b) - 1 / 2), sq_nonneg (a * b - b * (a - b)), sq_nonneg (a - 2 * b), sq_nonneg (a^2 - 2), sq_nonneg (b - (a - b)), sq_nonneg (a - 2 * b), sq_nonneg (b^2 - 1 / 2), sq_nonneg ( (a - b) ^2 - 1 / 2), mul_pos ha (show 0 < a - b by linarith), mul_pos hb (show 0 < a - b by linarith), mul_pos ha hb ]
    apply div_nonneg
    linarith [h4]
    all_goals
      positivity
  linarith