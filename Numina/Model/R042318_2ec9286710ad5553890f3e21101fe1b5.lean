import Mathlib

theorem calculus_13562 : Real.cos (36 * Real.pi / 180) - Real.cos (72 * Real.pi / 180) = 1 / 2 := by 
  have h1 : 36 * Real.pi / 180 = Real.pi / 5 := by 
    ring_nf 
  have h2 : 72 * Real.pi / 180 = 2 * Real.pi / 5 := by 
    ring_nf 
  rw [h1, h2]
  have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    have h4 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [Real.cos_pi_div_five]
    linarith 
  have h4 : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by 
    have h5 : Real.cos (2 * Real.pi / 5) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]
      ring_nf 
    rw [h5, h3]
    nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  rw [h3, h4]
  field_simp 
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]