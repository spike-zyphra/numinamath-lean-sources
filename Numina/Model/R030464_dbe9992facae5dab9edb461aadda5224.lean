import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_12174 {z : ℂ} (hz : z = exp (I * 2 * π / 3)) :
    z^3 + z^2 = 1 / 2 - Real.sqrt 3 / 2 * I := by
  rw [hz]
  have h1 : (exp (I * 2 * π / 3)) ^ 3 = 1 := by
    have h3 : (exp (I * 2 * π / 3)) ^ 3 = exp (3 * (I * 2 * π / 3)) := by
      rw [← Complex.exp_nat_mul]
      all_goals ring_nf
    rw [h3]
    have h4 : 3 * (I * 2 * π / 3) = I * (2 * π) := by
      ring_nf
    rw [h4]
    have h5 : exp (I * (2 * π)) = 1 := by
      rw [show I * (2 * π) = (2 * π) * I by ring_nf]
      rw [Complex.exp_two_pi_mul_I]
    exact h5
  have h2 : (exp (I * 2 * π / 3)) ^ 2 = exp (I * 4 * π / 3) := by
    have h3 : (exp (I * 2 * π / 3)) ^ 2 = exp (2 * (I * 2 * π / 3)) := by
      rw [← Complex.exp_nat_mul]
      all_goals ring_nf
    rw [h3]
    ring_nf
  rw [h1, h2]
  have h4 : exp (I * 4 * π / 3) = -1/2 - Real.sqrt 3 / 2 * I := by
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_add, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    constructor
    · -- Compute real part
      have h5 : Real.cos (4 * π / 3) = -1 / 2 := by
        have h7 : 4 * π / 3 = Real.pi + Real.pi / 3 := by
          linarith [Real.pi_pos]
        rw [h7]
        have h8 : Real.cos (Real.pi + Real.pi / 3) = -Real.cos (Real.pi / 3) := by
          rw [Real.cos_add]
          rw [Real.cos_pi, Real.sin_pi]
          ring
        rw [h8]
        have h9 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
        rw [h9]
        all_goals linarith
      linarith
    · -- Compute imaginary part
      have h10 : Real.sin (4 * π / 3) = -Real.sqrt 3 / 2 := by
        have h7 : 4 * π / 3 = Real.pi + Real.pi / 3 := by
          linarith [Real.pi_pos]
        rw [h7]
        have h11 : Real.sin (Real.pi + Real.pi / 3) = -Real.sin (Real.pi / 3) := by
          rw [Real.sin_add]
          rw [Real.cos_pi, Real.sin_pi]
          ring
        rw [h11]
        have h12 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        rw [h12]
        all_goals ring_nf
      linarith
  rw [h4]
  all_goals
    ring_nf