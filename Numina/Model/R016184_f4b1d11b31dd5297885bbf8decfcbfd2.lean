import Mathlib.Tactic

theorem inequalities_274079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c ≤ 3 := by 
  by_contra h1
  push_neg at h1
  have h2 : a < 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : b < 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h4 : c < 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  by_cases h5 : a ≥ 2
  · -- Assume a ≥ 2
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (c - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb),
              mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc)]
  by_cases h6 : b ≥ 2
  · -- Assume b ≥ 2
    nlinarith [sq_nonneg (b - 2), sq_nonneg (a - 1), sq_nonneg (c - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb),
              mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc)]
  by_cases h7 : c ≥ 2
  · -- Assume c ≥ 2
    nlinarith [sq_nonneg (c - 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb),
              mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc)]
  -- All variables < 2
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a * b - c * a), sq_nonneg (a * c - b * a), sq_nonneg (b * c - a * b)]