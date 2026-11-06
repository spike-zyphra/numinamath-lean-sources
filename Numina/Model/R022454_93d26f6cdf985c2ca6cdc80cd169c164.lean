import Mathlib

theorem algebra_302171 : (3 * Real.sqrt 15 - Real.sqrt 10 - 2 * Real.sqrt 6 + 3 * Real.sqrt 3 - Real.sqrt 2 + 18) /
    (Real.sqrt 5 + 2 * Real.sqrt 3 + 1) = 3 * Real.sqrt 3 - Real.sqrt 2 := by

  have h1 : Real.sqrt 15 = Real.sqrt 5 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h2 : Real.sqrt 10 = Real.sqrt 5 * Real.sqrt 2 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  
  have h3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  
  rw [h1, h2, h3]
  
  have h4 : Real.sqrt 5 > 0 := by 
    apply Real.sqrt_pos.mpr
    norm_num
  
  have h5 : Real.sqrt 3 > 0 := by 
    apply Real.sqrt_pos.mpr
    norm_num
  
  have h6 : Real.sqrt 2 > 0 := by 
    apply Real.sqrt_pos.mpr 
    norm_num
  
  have h7 : Real.sqrt 5 + 2 * Real.sqrt 3 + 1 > 0 := by
    linarith [h4, h5]

  field_simp [h7]
  nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
            sq_nonneg (Real.sqrt 5 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 - 1), 
            Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), 
            Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), 
            Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), 
            mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 3), 
            mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 2), 
            mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)
          ]