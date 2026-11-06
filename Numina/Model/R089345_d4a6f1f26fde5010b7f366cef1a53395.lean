import Mathlib

theorem algebra_177005 {a : ℝ} (ha : a * Real.logb 9 3 = 1) : (4 : ℝ) ^ (-a) = 1 / 16 := by
  have h1 : Real.logb 9 3 = 1 / 2 := by 
    rw [Real.logb]
    have h2 : Real.log 9 = 2 * Real.log 3 := by 
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      simp [Real.log_pow]
      all_goals linarith

    rw [h2]

    have h3 : Real.log 3 ≠ 0 := by 
      positivity

    field_simp [h3]
    <;> ring_nf <;> norm_num

  have ha2 : a = 2 := by 
    rw [h1] at ha
    linarith

  rw [ha2]
  norm_num
  <;> ring_nf <;> norm_num