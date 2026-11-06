import Mathlib

open Real Set
open scoped Real

theorem algebra_164078 : cos (36 * π / 180) = (sqrt 5 + 1) / 4 ∧
    sin (18 * π / 180) = (sqrt 5 - 1) / 4 := by
  have h1 : cos (36 * π / 180) = (sqrt 5 + 1) / 4 := by 
    have h2 : 36 * π / 180 = π / 5 := by 
      ring_nf 
    rw [h2]
    have h3 : cos (π / 5) = (1 + sqrt 5) / 4 := by 
      rw [cos_pi_div_five]
    have h4 : cos (π / 5) = (sqrt 5 + 1) / 4 := by 
      linarith [h3] 
    exact_mod_cast h4 
  have h2 : sin (18 * π / 180) = (sqrt 5 - 1) / 4 := by 
    have h3 : 18 * π / 180 = π / 10 := by 
      ring_nf 
    rw [h3]
    have h11 : sin (π / 10) = (sqrt 5 - 1) / 4 := by 
      have h100 : sin (π / 10) ^ 2 + cos (π / 10) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (π / 10)
      have h101 : cos (π / 5) = 2 * cos (π / 10) ^ 2 - 1 := by 
        rw [show π / 5 = 2 * (π / 10) by ring]
        rw [cos_two_mul]
      have h111 : cos (π / 5) = (1 + sqrt 5) / 4 := by 
        rw [cos_pi_div_five]
      rw [h101] at h111
      have h112 : cos (π / 10) ^ 2 = 1 - sin (π / 10) ^ 2 := by 
        linarith [h100]
      rw [h112] at h111
      have h102 : sin (π / 10) > 0 := by 
        apply sin_pos_of_pos_of_lt_pi 
        linarith [Real.pi_pos]
        linarith [Real.pi_pos]
      have h51 : sin (π / 10) ^ 2 = (3 - sqrt 5) / 8 := by 
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h100, h111]
      have h61 : sin (π / 10) - (sqrt 5 - 1) / 4 = 0 := by
        nlinarith [sq_nonneg (sin (π / 10) - (sqrt 5 - 1) / 4), sq_nonneg (sqrt 5 - 1), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      linarith 
    exact h11
  constructor 
  · exact h1 
  · exact h2