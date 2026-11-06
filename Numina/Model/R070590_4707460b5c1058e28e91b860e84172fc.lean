import Mathlib

theorem algebra_182600 : √(22 + 2 * √21) + √(22 - 2 * √21) = 2 * √21 := by
  have h1 : √(22 + 2 * √21) = √21 + 1 := by
    have h2 : (√21 + 1) ^ 2 = 22 + 2 * √21 := by
      calc
        (√21 + 1) ^ 2 = (√21) ^ 2 + 2 * √21 + 1 := by ring
        _ = 21 + 2 * √21 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
        _ = 22 + 2 * √21 := by ring
    have h3 : 0 ≤ √21 + 1 := by
      have h4 : 0 ≤ √21 := Real.sqrt_nonneg 21
      linarith
    rw [← h2]
    rw [Real.sqrt_sq h3]
  
  have h4 : √(22 - 2 * √21) = √21 - 1 := by
    have h5 : (√21 - 1) ^ 2 = 22 - 2 * √21 := by
      calc
        (√21 - 1) ^ 2 = (√21) ^ 2 - 2 * √21 + 1 := by ring
        _ = 21 - 2 * √21 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
        _ = 22 - 2 * √21 := by ring
    have h6 : 0 ≤ √21 - 1 := by
      have h7 : √21 ≥ √1 := Real.sqrt_le_sqrt (by norm_num)
      have h8 : √1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith [h7, h8]
    rw [← h5]
    rw [Real.sqrt_sq h6]

  rw [h1, h4]
  ring