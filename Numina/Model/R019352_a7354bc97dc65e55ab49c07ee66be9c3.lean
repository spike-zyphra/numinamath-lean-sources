import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_13428 {z : ℂ} (hz : z = Real.sqrt 2 * exp (11 * Real.pi * I / 4)) :
    z = -1 + I := by
  rw [hz]
  have h1 : 11 * Real.pi * I / 4 = 2 * Real.pi * I + (3 * Real.pi * I / 4) := by 
    ring_nf
  rw [h1]
  have h2 : exp (2 * Real.pi * I + (3 * Real.pi * I / 4)) = exp (3 * Real.pi * I / 4) := by
    rw [show 2 * Real.pi * I + (3 * Real.pi * I / 4) = (3 * Real.pi * I / 4) + (2 * Real.pi * I) by ring]
    have h3 : exp ((3 * Real.pi * I / 4) + (2 * Real.pi * I)) = exp (3 * Real.pi * I / 4) * exp (2 * Real.pi * I) := by 
      rw [exp_add]
    rw [h3]
    have h4 : exp (2 * Real.pi * I) = 1 := by 
      have h5 : exp (2 * Real.pi * I) = 1 := by 
        rw [exp_two_pi_mul_I]
      exact h5
    rw [h4]
    all_goals simp
  rw [h2]
  simp [Complex.ext_iff, exp_re, exp_im]
  have h3 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    have h4 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
    rw [h4]
    rw [Real.cos_pi_sub]
    have h5 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    linarith
  have h4 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by 
    have h5 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
    rw [h5]
    rw [Real.sin_pi_sub]
    have h6 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    linarith
  -- Compute real and imaginary parts.
  constructor
  · -- Show that the real part is -1
    have h5 : Real.sqrt 2 * Real.cos (3 * Real.pi / 4) = -1 := by
      rw [h3]
      have h6 : Real.sqrt 2 * (-Real.sqrt 2 / 2) = -1 := by
        calc
          Real.sqrt 2 * (-Real.sqrt 2 / 2) = - (Real.sqrt 2 * Real.sqrt 2) / 2 := by ring
          _ = - (2) / 2 := by 
            rw [Real.mul_self_sqrt]
            all_goals positivity
          _ = -1 := by norm_num
      linarith
    linarith [h5]
  · -- Show that the imaginary part is 1
    have h6 : Real.sqrt 2 * Real.sin (3 * Real.pi / 4) = 1 := by
      rw [h4]
      have h7 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
        calc
          Real.sqrt 2 * (Real.sqrt 2 / 2) = (Real.sqrt 2 * Real.sqrt 2) / 2 := by ring
          _ = (2) / 2 := by 
            rw [Real.mul_self_sqrt]
            all_goals positivity
          _ = (1) := by norm_num
      linarith
    linarith [h6]