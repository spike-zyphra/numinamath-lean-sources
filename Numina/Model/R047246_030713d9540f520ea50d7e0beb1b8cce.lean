import Mathlib

open Real Complex Polynomial

theorem calculus_14235 : (2 * exp (I * π / 9)) ^ 6 = -32 + 32 * I * Real.sqrt 3 := by
  have h4 : (2 * exp (I * π / 9)) ^ 6 = 64 * exp (I * (2 * π / 3)) := by
    calc
      (2 * exp (I * π / 9)) ^ 6 = 2 ^ 6 * (exp (I * π / 9) ^ 6) := by ring
      _ = 64 * (exp (I * π / 9) ^ 6) := by norm_num
      _ = 64 * exp (6 * (I * π / 9)) := by
        rw [← Complex.exp_nat_mul]
        all_goals ring_nf
      _ = 64 * exp (I * (2 * π / 3)) := by
        ring_nf
  rw [h4]

  have h2 : exp (I * (2 * π / 3)) = -1 / 2 + I * (Real.sqrt 3 / 2) := by
    rw [Complex.ext_iff]
    simp [Complex.exp_re, Complex.exp_im, show 2 * π / 3 = 2 * π / 3 by ring]
    constructor
    · -- Real part: cos(2π/3) = -1/2
      have h3 : Real.cos (2 * π / 3) = -1 / 2 := by
        have h2 : 2 * π / 3 = Real.pi - (π / 3) := by ring
        rw [h2]
        rw [Real.cos_pi_sub]
        norm_num
      linarith
    · -- Imaginary part: sin(2π/3) = sqrt(3)/2
      have h4 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
        have h2 : 2 * π / 3 = Real.pi - (π / 3) := by ring
        rw [h2]
        rw [Real.sin_pi_sub]
        have h3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        linarith
      linarith

  rw [h2]
  ring_nf