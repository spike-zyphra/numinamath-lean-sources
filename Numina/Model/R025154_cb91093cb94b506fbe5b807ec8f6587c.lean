import Mathlib

theorem algebra_198474 {x y : ℝ} (h1 : (6 : ℝ) ^ (x + y) = 36) (h2 : (6 : ℝ) ^ (x + 5 * y) = 216) :
    x = 7 / 4 := by 
  have eq1 : x + y = (2 : ℝ) := by
    have h3 : (6 : ℝ) ^ (x + y) = (6 : ℝ) ^ (2 : ℝ) := by 
      rw [h1]
      norm_num
    have h4 : x + y = (2 : ℝ) := by
      have h5 : x + y = (2 : ℝ) := by
        have h6 : (6 : ℝ) ^ (x + y) = (6 : ℝ) ^ (2 : ℝ) := h3
        have h7 : x + y = (2 : ℝ) := by
          have h8 : Real.logb (6 : ℝ) ((6 : ℝ) ^ (x + y)) = Real.logb (6 : ℝ) ((6 : ℝ) ^ (2 : ℝ)) := by 
            rw [h6]
          have h9 : Real.logb (6 : ℝ) ((6 : ℝ) ^ (x + y)) = x + y := by 
            rw [Real.logb_rpow]
            all_goals norm_num
          have h10 : Real.logb (6 : ℝ) ((6 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by 
            rw [Real.logb_rpow]
            all_goals norm_num
          rw [h9, h10] at h8 
          linarith 
        linarith 
      linarith 
    linarith [h4]
  have eq2 : x + 5 * y = (3 : ℝ) := by 
    have h3 : (6 : ℝ) ^ (x + 5 * y) = (6 : ℝ) ^ (3 : ℝ) := by 
      rw [h2]
      norm_num
    have h4 : x + 5 * y = (3 : ℝ) := by
      have h5 : x + 5 * y = (3 : ℝ) := by
        have h6 : (6 : ℝ) ^ (x + 5 * y) = (6 : ℝ) ^ (3 : ℝ) := h3
        have h7 : x + 5 * y = (3 : ℝ) := by
          have h8 : Real.logb (6 : ℝ) ((6 : ℝ) ^ (x + 5 * y)) = Real.logb (6 : ℝ) ((6 : ℝ) ^ (3 : ℝ)) := by 
            rw [h6]
          have h9 : Real.logb (6 : ℝ) ((6 : ℝ) ^ (x + 5 * y)) = x + 5 * y := by 
            rw [Real.logb_rpow]
            all_goals norm_num
          have h10 : Real.logb (6 : ℝ) ((6 : ℝ) ^ (3 : ℝ)) = (3 : ℝ) := by 
            rw [Real.logb_rpow]
            all_goals norm_num
          rw [h9, h10] at h8 
          linarith 
        linarith 
      linarith 
    linarith [h4]
  linarith [eq1, eq2]