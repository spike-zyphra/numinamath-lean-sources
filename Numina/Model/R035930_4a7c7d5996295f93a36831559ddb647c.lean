import Mathlib

open Real

theorem inequalities_300753 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : logb 10 a + logb 10 b + logb 10 c = 0) :
    1 < a / (a + 1) + b / (b + 1) + c / (c + 1) ∧
    a / (a + 1) + b / (b + 1) + c / (c + 1) < 2 := by
  have h1 : a * b * c = 1 := by
    have h2 : logb 10 a + logb 10 b + logb 10 c = logb 10 (a * b * c) := by
      simp [logb_mul, ha.ne.symm, hb.ne.symm, hc.ne.symm]
      all_goals nlinarith
    rw [h2] at h
    have h4 : logb 10 (a * b * c) = 0 := h
    have h5 : a * b * c > 0 := by positivity
    have h6 : (a * b * c) = (10 : ℝ) ^ (0 : ℝ) := by
      rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity)] at h4
      all_goals nlinarith
    have h8 : (10 : ℝ) ^ (0 : ℝ) = 1 := by
      norm_num
    rw [h8] at h6
    linarith
  constructor
  · -- Show that 1 < a / (a + 1) + b / (b + 1) + c / (c + 1)
    have h2 : a / (a + 1) + b / (b + 1) + c / (c + 1) - 1 > 0 := by
      have h3 : a / (a + 1) + b / (b + 1) + c / (c + 1) - 1 =
          (a * (b + 1) * (c + 1) + b * (a + 1) * (c + 1) + c * (a + 1) * (b + 1) - (a + 1) * (b + 1) * (c + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
        field_simp
        ring
      rw [h3]
      have h4 : a * (b + 1) * (c + 1) + b * (a + 1) * (c + 1) + c * (a + 1) * (b + 1) - (a + 1) * (b + 1) * (c + 1) > 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1
        ]
      apply div_pos
      linarith
      all_goals positivity
    linarith
  · -- Show that a / (a + 1) + b / (b + 1) + c / (c + 1) < 2
    have h2 : a / (a + 1) + b / (b + 1) + c / (c + 1) - 2 < 0 := by
      have h3 : a / (a + 1) + b / (b + 1) + c / (c + 1) - 2 =
          (a * (b + 1) * (c + 1) + b * (a + 1) * (c + 1) + c * (a + 1) * (b + 1) - 2 * (a + 1) * (b + 1) * (c + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
        field_simp
        ring
      rw [h3]
      have h4 : a * (b + 1) * (c + 1) + b * (a + 1) * (c + 1) + c * (a + 1) * (b + 1) - 2 * (a + 1) * (b + 1) * (c + 1) < 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1
        ]
      apply div_neg_of_neg_of_pos
      linarith
      all_goals positivity
    linarith