import Mathlib

open Real

theorem inequalities_286692 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : logb 10 a + logb 10 b + logb 10 c = 0) :
    1 < (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) ∧
    (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) < 2 := by

  have h1 : a * b * c = 1 := by
    have h2 : logb 10 a + logb 10 b + logb 10 c = logb 10 (a * b * c) := by 
      simp [logb_mul, ha.ne.symm, hb.ne.symm, hc.ne.symm]
    rw [h2] at h 
    have h3 : logb 10 (a * b * c) = 0 := h 
    have h4 : a * b * c = (10 : ℝ) ^ (0 : ℝ) := by
      rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity) ] at h3
      · linarith 
      all_goals linarith 
    have h5 : (10 : ℝ) ^ (0 : ℝ) = 1 := by
      simp
    rw [h5] at h4
    linarith

  have h2 : 1 < (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) := by
    have h5 : a * b * c = 1 := h1
    have h7 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) > 1 := by
      have h8 : 0 < (a + 1) * (b + 1) * (c + 1) := by positivity
      have h10 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) - 1 > 0 := by
        have h11 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) - 1 =
            (a * (b + 1) * (c + 1) + b * (a + 1) * (c + 1) + c * (a + 1) * (b + 1) - (a + 1) * (b + 1) * (c + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
          field_simp
          ring
        rw [h11]
        apply div_pos
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h5, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
        all_goals positivity
      linarith
    linarith

  have h3 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) < 2 := by
    have h5 : a * b * c = 1 := h1
    have h7 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) < 2 := by
      have h8 : 0 < (a + 1) * (b + 1) * (c + 1) := by positivity
      have h10 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) - 2 < 0 := by
        have h11 : (a / (a + 1)) + (b / (b + 1)) + (c / (c + 1)) - 2 =
            (a * (b + 1) * (c + 1) + b * (a + 1) * (c + 1) + c * (a + 1) * (b + 1) - 2 * (a + 1) * (b + 1) * (c + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
          field_simp
          ring
        rw [h11]
        apply div_neg_of_neg_of_pos
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h5, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
        all_goals positivity
      linarith
    linarith

  constructor 
  · exact h2 
  · exact h3