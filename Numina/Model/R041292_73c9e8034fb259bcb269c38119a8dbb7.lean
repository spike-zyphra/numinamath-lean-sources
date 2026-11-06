import Mathlib

open scoped NNReal

theorem inequalities_295444 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 = c ^ 3) :
    a ^ 2 + b ^ 2 - c ^ 2 > 6 * (c - a) * (c - b) := by
  have hc_gt_a : c > a := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, pow_pos ha 3, pow_pos hb 3, pow_pos hc 3, h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have hc_gt_b : c > b := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, pow_pos ha 3, pow_pos hb 3, pow_pos hc 3, h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have hc_lt_ab : c < a + b := by
    have h1 : c ^ 3 < (a + b) ^ 3 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, pow_pos ha 3, pow_pos hb 3, pow_pos hc 3, h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h2 : c < a + b := by
      have h3 : c ^ 3 < (a + b) ^ 3 := h1
      have h4 : c > 0 := by linarith
      have h5 : a + b > 0 := by linarith
      by_contra h6
      push_neg at h6
      have h7 : c ^ 3 ≥ (a + b) ^ 3 := by
        have h8 : c ≥ a + b := h6
        have h9 : c ^ 3 ≥ (a + b) ^ 3 := by
          apply pow_le_pow_left
          all_goals linarith
        linarith
      nlinarith
    linarith

  have h1 : a ^ 2 + b ^ 2 - c ^ 2 - 6 * (c - a) * (c - b) > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (c - (a + b)), sq_nonneg (a^2 - b^2), sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < (a + b) by nlinarith),
      hc_gt_a, hc_gt_b, hc_lt_ab, h, pow_pos ha 3, pow_pos hb 3, pow_pos hc 3
    ]

  linarith [h1]