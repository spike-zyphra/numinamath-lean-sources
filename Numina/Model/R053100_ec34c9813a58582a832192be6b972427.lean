import Mathlib

theorem algebra_310325 : (20 + 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) +
    (20 - 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = 4 := by
  have h1 : (20 + 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = 2 + Real.sqrt 2 := by
    have h4 : ((20 + 14 * Real.sqrt 2) : ℝ) = (2 + Real.sqrt 2) ^ (3 : ℝ) := by
      have h5 : ((2 + Real.sqrt 2) : ℝ) ^ (3 : ℝ) = ((2 + Real.sqrt 2) ^ 3 : ℝ) := by
        norm_cast
      rw [h5]
      ring_nf
      have h6 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
        exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h7 : Real.sqrt 2 ^ 3 = (Real.sqrt 2) * (2 : ℝ) := by
        calc
          (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring_nf
          _ = (2 : ℝ) * Real.sqrt 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          _ = (Real.sqrt 2) * (2 : ℝ) := by ring_nf
      nlinarith [Real.sqrt_nonneg 2, h6, h7]
    have h9 : ((20 + 14 * Real.sqrt 2) : ℝ) ^ ((1 : ℝ) / 3) = ((2 + Real.sqrt 2) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [h4]
    rw [h9]
    have h10 : (((2 + Real.sqrt 2) : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = ((2 + Real.sqrt 2) : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 2]
    linarith
  have h5 : (20 - 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = 2 - Real.sqrt 2 := by
    have h4 : ((20 - 14 * Real.sqrt 2) : ℝ) = (2 - Real.sqrt 2) ^ (3 : ℝ) := by
      have h5 : ((2 - Real.sqrt 2) : ℝ) ^ (3 : ℝ) = ((2 - Real.sqrt 2) ^ 3 : ℝ) := by
        norm_cast
      rw [h5]
      ring_nf
      have h6 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
        exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h7 : Real.sqrt 2 ^ 3 = (Real.sqrt 2) * (2 : ℝ) := by
        calc
          (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring_nf
          _ = (2 : ℝ) * Real.sqrt 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          _ = (Real.sqrt 2) * (2 : ℝ) := by ring_nf
      nlinarith [Real.sqrt_nonneg 2, h6, h7]
    have h9 : ((20 - 14 * Real.sqrt 2) : ℝ) ^ ((1 : ℝ) / 3) = ((2 - Real.sqrt 2) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [h4]
    rw [h9]
    have h10 : (((2 - Real.sqrt 2) : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = ((2 - Real.sqrt 2) : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 2, show Real.sqrt 2 ≤ (2 : ℝ) by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)]]
    linarith
  rw [h1, h5]
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]