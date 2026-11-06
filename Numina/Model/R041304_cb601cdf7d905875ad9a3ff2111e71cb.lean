import Mathlib

open Complex

theorem calculus_22849 (z : ℂ) (θ : Real.Angle) (hz : z = 4 - √3 + (-1 - 4 * √3) * I) (hθ : θ = (-2 * Real.pi / 3 : ℝ)) : z * θ.toCircle = -8 + 2 * I := by
  rw [hz, hθ, Real.Angle.coe_toCircle, Real.Angle.cos_coe, Real.Angle.sin_coe]
  have h1 : Real.cos (-2 * Real.pi / 3 : ℝ) = -1/2 := by
    have h2 : Real.cos (-2 * Real.pi / 3 : ℝ) = Real.cos (2 * Real.pi / 3 : ℝ) := by
      have h4 : -2 * Real.pi / 3 = - (2 * Real.pi / 3 : ℝ) := by ring
      rw [h4]
      rw [Real.cos_neg]
    rw [h2]
    have h2 : Real.cos (2 * Real.pi / 3 : ℝ) = -1/2 := by
      have h3 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by
        linarith [Real.pi_pos]
      rw [h3]
      rw [Real.cos_pi_sub]
      norm_num
    linarith [h2]

  have h2 : Real.sin (-2 * Real.pi / 3 : ℝ) = - Real.sqrt 3 / 2 := by
    have h3 : Real.sin (-2 * Real.pi / 3 : ℝ) = - Real.sin (2 * Real.pi / 3 : ℝ) := by
      have h4 : Real.sin (-2 * Real.pi / 3 : ℝ) = - Real.sin (2 * Real.pi / 3 : ℝ) := by
        have h9 : Real.sin (-2 * Real.pi / 3 : ℝ) = - Real.sin (2 * Real.pi / 3 : ℝ) := by
          have h10 : Real.sin (-2 * Real.pi / 3 : ℝ) = - Real.sin (2 * Real.pi / 3 : ℝ) := by
            rw [show -2 * Real.pi / 3 = - (2 * Real.pi / 3 : ℝ) by ring]
            rw [Real.sin_neg]
          linarith [h10]
        linarith [h9]
      linarith [h4]
    have h4 : Real.sin (2 * Real.pi / 3 : ℝ) = Real.sqrt 3 / 2 := by
      have h3 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by
        linarith [Real.pi_pos]
      rw [h3]
      rw [Real.sin_pi_sub]
      have h2 : Real.sin (Real.pi / 3 : ℝ) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      linarith [h2]
    rw [h3, h4]
    all_goals ring

  rw [h1, h2]
  simp [Complex.ext_iff, pow_two, mul_add, mul_comm, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm, mul_assoc]
  ring_nf
  <;> norm_num [Real.sqrt_mul_self]
  all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]