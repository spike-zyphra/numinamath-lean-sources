import Mathlib
open Real

theorem algebra_97758 : (15:ℝ)^30 / 45^15 = 5^15 := by 
  have h1 : (45 : ℝ) ^ 15 = (15 : ℝ) ^ 15 * (3 : ℝ) ^ 15 := by
    have h2 : (45 : ℝ) ^ 15 = (15 * 3 : ℝ) ^ 15 := by norm_num
    rw [h2]
    rw [mul_pow]
  rw [h1]
  have h2 : (15 : ℝ) ^ 30 = (15 : ℝ) ^ 15 * (15 : ℝ) ^ 15 := by
    ring_nf
  rw [h2]
  have h3 : (15 : ℝ) ^ 15 = (5 : ℝ) ^ 15 * (3 : ℝ) ^ 15 := by
    have h4 : (15 : ℝ) ^ 15 = (5 * 3 : ℝ) ^ 15 := by norm_num
    rw [h4]
    rw [mul_pow]
  calc
    (15 : ℝ) ^ 15 * (15 : ℝ) ^ 15 / ((15 : ℝ) ^ 15 * (3 : ℝ) ^ 15) 
        = (15 : ℝ) ^ 15 / ( (3 : ℝ) ^ 15 ) := by
          field_simp [show (15 : ℝ) ^ 15 ≠ 0 by norm_num]
          <;> ring
    _ = ((5 : ℝ) ^ 15 * (3 : ℝ) ^ 15) / ((3 : ℝ) ^ 15) := by
      rw [h3]
    _ = (5 : ℝ) ^ 15 := by
      field_simp [show (3 : ℝ) ^ 15 ≠ 0 by norm_num]
      <;> ring