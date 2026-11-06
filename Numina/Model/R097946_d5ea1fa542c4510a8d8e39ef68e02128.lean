import Mathlib

theorem algebra_12899 : √(10 - √84) = √7 - √3 := by
  have h1 : (√7 - √3) ^ 2 = 10 - √84 := by
    have h2 : (√7 - √3) ^ 2 = 10 - 2 * √21 := by
      have h3 : (√7 - √3) ^ 2 = (√7) ^ 2 - 2 * (√7 * √3) + (√3) ^ 2 := by
        ring
      rw [h3]
      have h4 : (√7) ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
      have h5 : (√3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h6 : √7 * √3 = √21 := by
        rw [← Real.sqrt_mul (by norm_num)]
        norm_num
      rw [h4, h5, h6]
      nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show 0 ≤ (21 : ℝ) by norm_num)]
    have h9 : √84 = 2 * √21 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h9] at *
    linarith [Real.sqrt_nonneg 21]
  
  have h14 : (√7 - √3) ≥ 0 := by
    have h15 : √7 ≥ √3 := Real.sqrt_le_sqrt (by norm_num)
    linarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 3]

  have h13 : √(10 - √84) = √((√7 - √3) ^ 2) := by
    rw [h1]
  
  have h17 : √((√7 - √3) ^ 2) = √7 - √3 := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg h14]
    all_goals linarith
  
  rw [h17] at h13
  linarith