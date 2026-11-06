import Mathlib

theorem algebra_95751 : (27 ^ ((1 : ℝ) / 6) - √(6 + 3 / 4)) ^ 2 = 3 / 4 := by
  have h1 : (27 : ℝ) ^ ((1 : ℝ) / 6) = √3 := by
    have h2 : (27 : ℝ) ^ ((1 : ℝ) / 6) = ((3 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 6) := by norm_num
    rw [h2]
    rw [← Real.rpow_mul]
    norm_num
    rw [Real.sqrt_eq_rpow]
    all_goals norm_num
  
  have h3 : √(6 + (3 : ℝ) / 4) = (3 * √3) / 2 := by
    have h4 : (6 + (3 : ℝ) / 4) = (27 / 4 : ℝ) := by norm_num
    rw [h4]
    have h5 : √((27 / 4 : ℝ)) = (3 * √3) / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num [Real.sq_sqrt, mul_nonneg, show (0 : ℝ) ≤ (3 : ℝ) by norm_num]
    exact h5
  
  rw [h1, h3]
  
  have h5 : (√3 - (3 * √3) / 2) = - (√3) / 2 := by
    ring_nf
    <;> field_simp
    <;> ring

  rw [h5]
  have h7 : (- (√3) / 2 : ℝ) ^ 2 = (√3 / 2) ^ 2 := by
    ring

  rw [h7]
  have h8 : (√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
    calc
      (√3 / 2 : ℝ) ^ 2 = (√3 ^ 2) / 4 := by ring
      _ = (3) / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      _ = 3 / 4 := by norm_num
  
  rw [h8]
  all_goals nlinarith