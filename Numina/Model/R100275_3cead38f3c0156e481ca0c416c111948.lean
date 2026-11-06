import Mathlib

theorem algebra_13646 : Real.sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by 
  have h1 : Real.sin (Real.pi / 12) = Real.sin (Real.pi / 4 - Real.pi / 6) := by 
    ring_nf
  rw [h1]
  rw [Real.sin_sub]
  have h2 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h4 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  have h5 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  rw [h2, h3, h4, h5]
  have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    calc
      Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3) := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 6 := by norm_num
  linarith [h6]
  all_goals ring_nf <;> norm_num
  <;> ring_nf <;> norm_num