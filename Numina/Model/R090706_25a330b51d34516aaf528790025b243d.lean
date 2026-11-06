import Mathlib

theorem algebra_16495 (y : ℝ) (hy : 3 ≤ 2 * y - 3 ∧ 0 ≤ 1 + Real.sqrt (2 * y - 3)) (h : Real.sqrt (1 + Real.sqrt (2 * y - 3)) = Real.sqrt 6) :
    y = 14 := by 
  have h1 : 3 ≤ 2 * y - 3 := hy.left
  have h2 : 0 ≤ 1 + Real.sqrt (2 * y - 3) := hy.right
  have h3 : Real.sqrt (1 + Real.sqrt (2 * y - 3)) = Real.sqrt 6 := h
  have h4 : 1 + Real.sqrt (2 * y - 3) = 6 := by
    calc
      1 + Real.sqrt (2 * y - 3) = (Real.sqrt (1 + Real.sqrt (2 * y - 3))) ^ 2 := by 
        rw [Real.sq_sqrt]
        all_goals linarith 
      _ = (Real.sqrt 6) ^ 2 := by rw [h3]
      _ = 6 := by 
        rw [Real.sq_sqrt]
        all_goals norm_num
  have h5 : Real.sqrt (2 * y - 3) = 5 := by 
    linarith [h4] 
  have h6 : 2 * y - 3 = 25 := by 
    calc
      2 * y - 3 = (Real.sqrt (2 * y - 3)) ^ 2 := by 
        rw [Real.sq_sqrt]
        all_goals linarith 
      _ = 5 ^ 2 := by rw [h5]
      _ = 25 := by norm_num
  linarith