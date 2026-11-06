import Mathlib

theorem algebra_185885 (z : ℂ) (hz : z = 3 - Real.sqrt 3 * .I) :
    (z * Complex.exp (-Complex.I * Real.pi / 3)) = -2 * Real.sqrt 3 * .I := by
  rw [hz]
  have h1 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h4 : Real.sin (- Real.pi / 3) = - Real.sqrt 3 / 2 := by
    have h3 : Real.sin (- Real.pi / 3) = - Real.sin (Real.pi / 3) := by
      rw [show - Real.pi / 3 = - (Real.pi / 3) by ring]
      simp [Real.sin_neg]
    rw [h3, h1]
    all_goals nlinarith
  have h5 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h7 : Real.cos (- Real.pi / 3) = 1 / 2 := by
    have h8 : Real.cos (- Real.pi / 3) = Real.cos (Real.pi / 3) := by
      rw [show - Real.pi / 3 = - (Real.pi / 3) by ring]
      rw [Real.cos_neg]
    rw [h8, h5]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, mul_add, mul_comm, mul_assoc, h4, h7]
  ring_nf
  <;> norm_num [Real.sqrt_mul_self, mul_add, mul_comm, mul_assoc]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]