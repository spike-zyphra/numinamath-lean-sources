import Mathlib

open Real

theorem algebra_303768 :
    ((sqrt 2 + sqrt 6) / sqrt (2 + sqrt 3) - 2) * (2005^2 - 2005 * 2004 + 2004^2) = 0 := by
  have h1 : (sqrt 2 + sqrt 6) / sqrt (2 + sqrt 3) - 2 = 0 := by
    have h2 : sqrt 6 = sqrt 2 * sqrt 3 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h3 : sqrt (2 + Real.sqrt 3) > 0 := by
      apply Real.sqrt_pos.mpr
      have h4 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]

    have h5 : (sqrt 2 + sqrt 6) ^ 2 = 4 * (2 + Real.sqrt 3) := by
      have h6 : sqrt 6 = sqrt 2 * sqrt 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h6]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_pos (Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))) (Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)))]

    have h9 : sqrt (2 + Real.sqrt 3) ^ 2 = 2 + Real.sqrt 3 := by
      rw [Real.sq_sqrt]
      positivity

    have h4 : (sqrt 2 + sqrt 6) / sqrt (2 + Real.sqrt 3) = 2 := by
      have h11 : sqrt 2 + sqrt 6 = 2 * Real.sqrt (2 + Real.sqrt 3) := by
        have h12 : (sqrt 2 + sqrt 6) ^ 2 = (2 * Real.sqrt (2 + Real.sqrt 3)) ^ 2 := by
          have h13 : (2 * Real.sqrt (2 + Real.sqrt 3)) ^ 2 = 4 * (Real.sqrt (2 + Real.sqrt 3) ^ 2) := by ring
          rw [h13]
          rw [h9]
          nlinarith
        have h16 : sqrt 2 + sqrt 6 ≥ 0 := by positivity
        have h17 : 2 * Real.sqrt (2 + Real.sqrt 3) ≥ 0 := by positivity
        have h18 : sqrt 2 + sqrt 6 = 2 * Real.sqrt (2 + Real.sqrt 3) := by
          nlinarith [sq_nonneg (sqrt 2 + sqrt 6 - 2 * Real.sqrt (2 + Real.sqrt 3)), h12]
        exact_mod_cast h18

      have h5 : sqrt (2 + Real.sqrt 3) > 0 := h3
      field_simp at *
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 + Real.sqrt 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + Real.sqrt 3) by positivity)]
    
    linarith
  rw [h1]
  norm_num
  all_goals nlinarith