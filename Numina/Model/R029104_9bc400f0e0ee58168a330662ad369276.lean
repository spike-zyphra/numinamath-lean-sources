import Mathlib

theorem inequalities_125426 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ 36 := by
  have h1 : a ^ 2 + 1 ≥ 2 * a := by
    nlinarith [sq_nonneg (a - 1)]
  -- b^3 + 2 \geq 3 b
  have h2 : b ^ 3 + 2 ≥ 3 * b := by
    have h3 : b ^ 3 + 2 - 3 * b ≥ 0 := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 2), sq_nonneg (b * b), mul_pos hb hb]
    linarith
  -- c^6 +5 \geq 6c
  have h3 : c ^ 6 + 5 ≥ 6 * c := by
    nlinarith [sq_nonneg (c ^ 2 - 1), sq_nonneg (c ^ 2 - c), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (c ^ 2 + 1), sq_nonneg (c ^ 3 - 1), sq_nonneg (c ^ 3 - c), sq_nonneg (c * c - 1), sq_nonneg (c * c * c - 1), mul_pos hc hc, mul_pos hc (show 0 < c + 1 by linarith), sq_nonneg (c - 1), sq_nonneg (c * c - 1), sq_nonneg (c * c * c - 1), sq_nonneg (c ^ 2 - 1), sq_nonneg (c ^ 2 - c), sq_nonneg (c ^ 2 * c), sq_nonneg (c * c * c * c * c * c - 1), sq_nonneg (c ^ 2 - 1)]
  have h4 : (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ (2 * a) * (3 * b) * (6 * c) := by
    apply mul_le_mul
    · apply mul_le_mul
      all_goals nlinarith [h1, h2, h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    all_goals
      nlinarith [h1, h2, h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    all_goals positivity
  have h4' : (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ 36 * (a * b * c) := by
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : 36 * (a * b * c) = 36 := by
    rw [show a * b * c = 1 by linarith [habc]]
    all_goals norm_num
  linarith [h4', h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]