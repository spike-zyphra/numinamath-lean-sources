import Mathlib

theorem algebra_95980 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : Real.logb 2 a + Real.logb 2 b ≥ 6) :
    a + b ≥ 16 := by
  have h1 : Real.logb 2 a + Real.logb 2 b = Real.logb 2 (a * b) := by
    rw [Real.logb_mul (by positivity) (by positivity)]
  rw [h1] at h
  have h2 : a * b ≥ (2:ℝ) ^ (6:ℝ) := by
    by_contra h2
    push_neg at h2
    have h3 : Real.logb 2 (a * b) < 6 := by
      have h4 : a * b > 0 := mul_pos ha hb
      have h5 : Real.logb 2 (a * b) < 6 := by
        have h6 : a * b < (2:ℝ) ^ (6:ℝ) := h2
        have h7 : Real.logb 2 (a * b) < Real.logb 2 ((2:ℝ) ^ (6:ℝ)) := by
          apply Real.logb_lt_logb
          all_goals nlinarith
        have h8 : Real.logb 2 ((2:ℝ) ^ (6:ℝ)) = (6:ℝ) := by
          simp [Real.logb_rpow]
        linarith
      linarith
    linarith
  have h5 : a * b ≥ (64 : ℝ) := by
    have h6 : (2 : ℝ) ^ (6 : ℝ) = (64 : ℝ) := by norm_num
    linarith [h2, h6]
  nlinarith [sq_nonneg (a - b), h5, mul_pos ha hb]