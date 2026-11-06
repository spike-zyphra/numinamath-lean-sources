import Mathlib

open Real Complex Polynomial

theorem calculus_12606 : exp (11 * π * I / 2) = -I := by
  have h1 : exp (11 * π * I / 2) = exp (5 * π * I + π * I / 2) := by
    ring_nf
    <;> simp [mul_div]
    <;> ring_nf
  have h2 : exp (5 * π * I) = -1 := by
    have h3 : 5 * π * I = 2 * π * I + 2 * π * I + π * I := by ring_nf
    rw [h3]
    have h4 : exp (2 * π * I + 2 * π * I + π * I) = exp (2 * π * I + 2 * π * I) * exp (π * I) := by
      rw [show 2 * π * I + 2 * π * I + π * I = (2 * π * I + 2 * π * I) + π * I by ring]
      rw [Complex.exp_add]
    have h5 : exp (2 * π * I + 2 * π * I) = exp (2 * π * I) * exp (2 * π * I) := by
      rw [show 2 * π * I + 2 * π * I = (2 * π * I) + (2 * π * I) by ring]
      rw [Complex.exp_add]
    rw [h4, h5]
    have h6 : exp (2 * π * I) = 1 := by
      rw [Complex.exp_two_pi_mul_I]
      <;> norm_num
    have h7 : exp (π * I) = -1 := by
      rw [Complex.exp_pi_mul_I]
      <;> norm_num
    simp [h6, h7]
    <;> norm_num
    <;> ring_nf <;> norm_num

  have h3 : exp (π * I / 2) = I := by
    have h4 : π * I / 2 = (π / 2) * I := by ring_nf
    rw [h4]
    simp [Complex.exp_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    <;> ring_nf <;> norm_num

  have h4 : exp (5 * π * I + π * I / 2) = exp (5 * π * I) * exp (π * I / 2) := by 
    rw [Complex.exp_add]
    all_goals norm_num

  rw [h1, h4, h2, h3]
  all_goals norm_num
  all_goals ring_nf <;> norm_num