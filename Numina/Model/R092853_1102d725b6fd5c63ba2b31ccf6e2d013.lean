import Mathlib

open Real

theorem algebra_291049 (x : ℝ) :
    4 * cos x * cos (x + π / 3) * cos (x - π / 3) = cos (3 * x) := by
  have h1 : cos (x + π / 3) = cos x * cos (π / 3) - sin x * sin (π / 3) := by
    rw [cos_add]
  have h2 : cos (x - π / 3) = cos x * cos (π / 3) + sin x * sin (π / 3) := by
    rw [cos_sub]
  have h3 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h4 : sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h7 : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
    rw [cos_three_mul]
  rw [h1, h2, h3, h4]
  rw [h7]
  have h5 : sin x ^ 2 = 1 - cos x ^ 2 := by
    have h6 : cos x ^ 2 + sin x ^ 2 = 1 := by
      exact cos_sq_add_sin_sq x
    linarith
  have h8 : Real.sqrt 3 ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    norm_num
  ring_nf
  <;> simp [pow_two, pow_three, h5, h8, mul_add, mul_sub, add_mul, sub_mul, mul_comm]
  <;> ring_nf
  <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0)] 
  <;> ring