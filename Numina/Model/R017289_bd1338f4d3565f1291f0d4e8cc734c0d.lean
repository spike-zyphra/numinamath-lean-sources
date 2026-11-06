import Mathlib

theorem algebra_608 : (12 * √48 / (5 * √72)) = (4 * √6) / 5 := by

  have h1 : √48 = 4 * √3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h2 : √72 = 6 * √2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  
  have h3 : (12 * √48 / (5 * √72)) = (48 * √3) / (30 * √2) := by 
    rw [h1, h2]
    field_simp
    <;> ring_nf

  have h4 : (48 * √3) / (30 * √2) = (4 * √6) / 5 := by
    have h5 : √3 * √2 = √6 := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num

    field_simp [(show √2 ≠ 0 by positivity)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
        h5, Real.sqrt_nonneg (6: ℝ)]
  
  rw [h3]
  exact h4