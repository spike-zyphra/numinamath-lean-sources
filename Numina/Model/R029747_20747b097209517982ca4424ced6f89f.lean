import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156852 :
  ∫ x in (0)..(π/3), sin x = 1/2 ∧
  ∫ x in (π/6)..(π/2), cos x = 1/2 ∧
  ∫ x in (0)..(π/4), cos (2*x) = 1/2 := by 
  constructor
  · -- Proof that ∫ x in (0)..(π/3), sin x = 1/2
    have h1 : ∫ x in (0)..(π / 3), sin x = 1 / 2 := by
      simp [intervalIntegral.integral_const, Real.sin_pi_div_three, Real.cos_pi_div_three, Real.cos_zero]
      all_goals ring
    exact h1
  constructor
  · -- Proof that ∫ x in (π/6)..(π/2), cos x = 1/2 
    have h2 : ∫ x in (π / 6)..(π / 2), cos x = 1 / 2 := by
      simp [intervalIntegral.integral_const, Real.sin_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_six]
      all_goals ring
    exact h2
  · -- Proof that ∫ x in (0)..(π/4), cos (2*x) = 1/2
    have h3 : ∫ x in (0)..(π / 4), cos (2 * x) = 1 / 2 := by
      have h3 : ∫ x in (0)..(π / 4), cos (2 * x) = (1 / 2) * sin (2 * (π / 4)) - (1 / 2) * sin (2 * (0 : ℝ)) := by 
        simp [intervalIntegral.integral_const, mul_comm]
        <;> ring_nf <;> norm_num [Real.sin_pi_div_two]
      rw [h3]
      have h4 : sin (2 * (π / 4)) = 1 := by 
        have h5 : 2 * (π / 4) = π / 2 := by ring
        rw [h5]
        exact sin_pi_div_two
      have h6 : sin (2 * (0 : ℝ)) = 0 := by 
        simp 
      rw [h4, h6]
      all_goals ring_nf
    exact h3