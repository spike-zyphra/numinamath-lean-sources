import Mathlib

theorem algebra_286470 : (2 * √12 - 4 * √27 + 3 * √75 + 7 * √8 - 3 * √18) * (4 * √48 - 3 * √27 - 5 * √18 + 2 * √50) = 97 := by
  have h1 : √12 = 2 * √3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf
    <;> norm_num
  
  have h2 : √27 = 3 * √3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf
    <;> norm_num
  
  have h3 : √75 = 5 * √3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf
    <;> norm_num
  
  have h4 : √8 = 2 * √2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf
    <;> norm_num
  
  have h5 : √18 = 3 * √2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf
    <;> norm_num
  
  have h6 : √48 = 4 * √3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num
  
  have h7 : √50 = 5 * √2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num
  
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ),
    Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num),
    mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (2 : ℝ))]