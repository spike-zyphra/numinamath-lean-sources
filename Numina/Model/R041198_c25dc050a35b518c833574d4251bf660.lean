import Mathlib
set_option maxHeartbeats 400000000
theorem algebra_177177 (x : ℝ) (hx : x ≥ 11) :
    Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) =
    Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) ↔ x = 13 := by 
  constructor
  · -- Assume the equation holds, prove x = 13
    intro h_eq
    have h1 : Real.sqrt ((x - 2) / 11) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : Real.sqrt ((x - 3) / 10) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : Real.sqrt ((x - 11) / 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : Real.sqrt ((x - 10) / 3) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h5 : (Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10)) ^ 2 = (Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3)) ^ 2 := by 
      have h6 : Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) = Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) := h_eq
      rw [h6]
    have h61 : (Real.sqrt ((x - 2) / 11)) ^ 2 = (x - 2) / 11 := by
      apply Real.sq_sqrt
      linarith
    have h62 : (Real.sqrt ((x - 3) / 10)) ^ 2 = (x - 3) / 10 := by
      apply Real.sq_sqrt
      linarith
    have h63 : (Real.sqrt ((x - 11) / 2)) ^ 2 = (x - 11) / 2 := by
      apply Real.sq_sqrt
      linarith
    have h64 : (Real.sqrt ((x - 10) / 3)) ^ 2 = (x - 10) / 3 := by
      apply Real.sq_sqrt
      linarith
    have h6 : (Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10)) ^ 2 =
        (Real.sqrt ((x - 2) / 11)) ^ 2 + (Real.sqrt ((x - 3) / 10)) ^ 2 + 2 * (Real.sqrt ((x - 2) / 11) * Real.sqrt ((x - 3) / 10)) := by ring
    have h7 : (Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3)) ^ 2 =
        (Real.sqrt ((x - 11) / 2)) ^ 2 + (Real.sqrt ((x - 10) / 3)) ^ 2 + 2 * (Real.sqrt ((x - 11) / 2) * Real.sqrt ((x - 10) / 3)) := by ring
    rw [h6, h7] at h5
    rw [h61, h62, h63, h64] at h5
    nlinarith [Real.sqrt_nonneg ((x - 2) / 11), Real.sqrt_nonneg ((x - 3) / 10), 
      Real.sqrt_nonneg ((x - 11) / 2), Real.sqrt_nonneg ((x - 10) / 3), 
      sq_nonneg (Real.sqrt ((x - 2) / 11) - Real.sqrt ((x - 11) / 2)), 
      sq_nonneg (Real.sqrt ((x - 3) / 10) - Real.sqrt ((x - 10) / 3)), 
      sq_nonneg (x - 13), 
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x - 2) / 11 by linarith), 
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x - 3) / 10 by linarith), 
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x - 11) / 2 by linarith), 
      Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x - 10) / 3 by linarith), 
      mul_nonneg (Real.sqrt_nonneg ((x - 2) / 11)) (Real.sqrt_nonneg ((x - 3) / 10)), 
      mul_nonneg (Real.sqrt_nonneg ((x - 11) / 2)) (Real.sqrt_nonneg ((x - 10) / 3))
    ]
  · -- Assume x = 13, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt ((13 - 2) / 11) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((13 - 3) / 10) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((13 - 11) / 2) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt ((13 - 10) / 3) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3, h4]
    all_goals norm_num