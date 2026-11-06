import Mathlib

theorem algebra_320986 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h₁ : a + Real.logb 10 a = 10) (h₂ : b + 10 ^ b = 10) :
    Real.logb 10 (a + b) = 1 := by

  have h3 : Real.logb 10 a = b := by
    by_cases h4 : Real.logb 10 a < b
    · -- Assume Real.logb 10 a < b
      have h4 : Real.logb 10 a < b := h4
      have h5 : a < (10 : ℝ) ^ b := by
        have h6 : Real.logb 10 a < b := h4
        have h7 : Real.logb 10 ((10 : ℝ) ^ b) = b := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h8 : Real.logb 10 a < Real.logb 10 ((10 : ℝ) ^ b) := by linarith [h6, h7]
        have h9 : a < ((10 : ℝ) ^ b) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by positivity) (by positivity)).mp at h8
          linarith
        linarith
      have h10 : a + b > 10 := by
        nlinarith [h₁, h4]
      have h11 : b + (10 : ℝ) ^ b = 10 := by linarith
      nlinarith [h11, h10, Real.rpow_pos_of_pos (show (0 : ℝ) < 10 by norm_num) b]
    · -- Real.logb 10 a ≥ b
      by_cases h5 : Real.logb 10 a > b
      · -- Assume Real.logb 10 a > b
        have h5 : Real.logb 10 a > b := h5
        have h6 : a > (10 : ℝ) ^ b := by
          have h7 : Real.logb 10 a > b := h5
          have h8 : Real.logb 10 ((10 : ℝ) ^ b) = b := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h9 : Real.logb 10 a > Real.logb 10 ((10 : ℝ) ^ b) := by linarith [h7, h8]
          have h10 : a > ((10 : ℝ) ^ b) := by
            apply (Real.logb_lt_logb_iff (by linarith) (by positivity) (by positivity)).mp at h9
            linarith
          linarith
        have h10 : a + b < (10 : ℝ) := by
          nlinarith [h₁, h5]
        have h11 : b + (10 : ℝ) ^ b = 10 := by linarith
        nlinarith [h11, h10, Real.rpow_pos_of_pos (show (0 : ℝ) < 10 by norm_num) b]
      · -- Real.logb 10 a = b
        linarith
  have h4 : a = (10 : ℝ) ^ b := by
    have h5 : Real.logb 10 a = b := h3
    have h6 : a = (10 : ℝ) ^ (Real.logb 10 a) := by
      field_simp [Real.rpow_logb, ha]
    rw [h5] at h6
    linarith
  have h5 : a + b = 10 := by
    have h6 : a = (10 : ℝ) ^ b := h4
    have h7 : b + (10 : ℝ) ^ b = 10 := by linarith
    nlinarith
  have h6 : Real.logb 10 (a + b) = 1 := by
    rw [show a + b = (10 : ℝ) by linarith [h5]]
    simp
  exact h6