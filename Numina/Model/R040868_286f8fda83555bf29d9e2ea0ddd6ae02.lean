import Mathlib

theorem algebra_94431 : (Real.sqrt 2 / (Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5)) = (Real.sqrt 6 + 3 + Real.sqrt 15) / 6 := by 
  have h1 : Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5 ≠ 0 := by 
    by_contra h
    have h2 : Real.sqrt 2 + Real.sqrt 3 = Real.sqrt 5 := by
      linarith
    have h3 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Real.sqrt 5) ^ 2 := by
      rw [show Real.sqrt 2 + Real.sqrt 3 = Real.sqrt 5 by linarith [h2]]
    have h4 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Real.sqrt 2) ^ 2 + (Real.sqrt 3) ^ 2 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by 
      ring
    have h5 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h6 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have h7 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
    have h8 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by 
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    have h9 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (5 + 2 * Real.sqrt 6 : ℝ) := by 
      rw [h4, h5, h6, h8]
      all_goals ring_nf
    rw [h9] at h3
    rw [h7] at h3
    have h10 : (Real.sqrt 6) = (0 : ℝ) := by 
      nlinarith 
    have h11 : Real.sqrt 6 > 0 := by 
      apply Real.sqrt_pos.mpr
      all_goals norm_num 
    linarith 
  -- Express sqrt 6 and sqrt 15 as products of other square roots
  have h123 : (Real.sqrt 6 : ℝ) = Real.sqrt 2 * Real.sqrt 3 := by
    have h1 : Real.sqrt 6 = Real.sqrt (2 * 3 : ℝ) := by norm_num
    rw [h1]
    rw [Real.sqrt_mul]
    all_goals norm_num 
  have h15 : (Real.sqrt 15 : ℝ) = Real.sqrt 3 * Real.sqrt 5 := by
    have h1 : Real.sqrt 15 = Real.sqrt (3 * 5: ℝ) := by norm_num 
    rw [h1]
    rw [Real.sqrt_mul]
    all_goals norm_num 
  rw [h123, h15]
  field_simp [h1]
  <;> ring_nf
  <;> simp [Real.sq_sqrt, mul_add, add_mul]
  <;> ring_nf 
  <;> norm_num
  all_goals nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5]