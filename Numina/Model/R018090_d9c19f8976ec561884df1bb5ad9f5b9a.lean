import Mathlib

theorem algebra_177364 (x : ℝ) (hx : x ≥ 11) :
    Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) =
    Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) ↔ x = 14 := by 
  constructor
  · -- Assume the equation holds, prove x = 14
    intro h_eq
    have h1 : Real.sqrt ((x - 3) / 11) ≥ 0 := Real.sqrt_nonneg ((x - 3) / 11)
    have h2 : Real.sqrt ((x - 4) / 10) ≥ 0 := Real.sqrt_nonneg ((x - 4) / 10)
    have h3 : Real.sqrt ((x - 11) / 3) ≥ 0 := Real.sqrt_nonneg ((x - 11) / 3)
    have h4 : Real.sqrt ((x - 10) / 4) ≥ 0 := Real.sqrt_nonneg ((x - 10) / 4)
    have h_eq1 : (Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10)) ^ 2 = (Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4)) ^ 2 := by
      rw [h_eq]
    have h_eq2 : (Real.sqrt ((x - 3) / 11)) ^ 2 = (x - 3) / 11 := by
      apply Real.sq_sqrt
      linarith
    have h_eq3 : (Real.sqrt ((x - 4) / 10)) ^ 2 = (x - 4) / 10 := by
      apply Real.sq_sqrt
      linarith
    have h_eq4 : (Real.sqrt ((x - 11) / 3)) ^ 2 = (x - 11) / 3 := by
      apply Real.sq_sqrt
      linarith
    have h_eq5 : (Real.sqrt ((x - 10) / 4)) ^ 2 = (x - 10) / 4 := by
      apply Real.sq_sqrt
      linarith
    have h_eq6 : (Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10)) ^ 2 =
      (Real.sqrt ((x - 3) / 11)) ^ 2 + (Real.sqrt ((x - 4) / 10)) ^ 2 + 2 * (Real.sqrt ((x - 3) / 11) * Real.sqrt ((x - 4) / 10)) := by
      ring
    have h_eq7 : (Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4)) ^ 2 =
      (Real.sqrt ((x - 11) / 3)) ^ 2 + (Real.sqrt ((x - 10) / 4)) ^ 2 + 2 * (Real.sqrt ((x - 11) / 3) * Real.sqrt ((x - 10) / 4)) := by 
      ring
    rw [h_eq6, h_eq7] at h_eq1
    rw [h_eq2, h_eq3, h_eq4, h_eq5] at h_eq1
    by_cases h : x > 14
    · -- Assume x > 14, derive contradiction
      nlinarith [Real.sqrt_nonneg ((x - 3) / 11), Real.sqrt_nonneg ((x - 4) / 10), 
        Real.sqrt_nonneg ((x - 11) / 3), Real.sqrt_nonneg ((x - 10) / 4), 
        mul_nonneg (Real.sqrt_nonneg ((x - 3) / 11)) (Real.sqrt_nonneg ((x - 4) / 10)), 
        mul_nonneg (Real.sqrt_nonneg ((x - 11) / 3)) (Real.sqrt_nonneg ((x - 10) / 4)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 3) / 11 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 4) / 10 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 11) / 3 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 10) / 4 by linarith)]
    · -- Assume x ≤ 14
      have h8 : x ≤ 14 := by linarith
      by_cases h' : x < 14
      · -- Assume x < 14, derive contradiction
        nlinarith [Real.sqrt_nonneg ((x - 3) / 11), Real.sqrt_nonneg ((x - 4) / 10), 
          Real.sqrt_nonneg ((x - 11) / 3), Real.sqrt_nonneg ((x - 10) / 4), 
          mul_nonneg (Real.sqrt_nonneg ((x - 3) / 11)) (Real.sqrt_nonneg ((x - 4) / 10)), 
          mul_nonneg (Real.sqrt_nonneg ((x - 11) / 3)) (Real.sqrt_nonneg ((x - 10) / 4)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 3) / 11 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 4) / 10 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 11) / 3 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 10) / 4 by linarith)]
      · -- x = 14
        linarith
  · -- Assume x = 14, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt ((14 - 3 : ℝ) / 11) = 1 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((14 - 4 : ℝ) / 10) = 1 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((14 - 11 : ℝ) / 3) = 1 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt ((14 - 10 : ℝ) / 4) = 1 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3, h4]
    all_goals linarith