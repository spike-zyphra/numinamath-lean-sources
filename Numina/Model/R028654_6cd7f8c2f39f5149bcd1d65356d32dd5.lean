import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_248757 (z : ℂ) (hz : z.re ≠ 0) :
    IsLeast {x | ∃ z : ℂ, z.re ≠ 0 ∧ x = (z^4).re / z.re^4} (-8) := by
  constructor
  · -- We verify with z = 1 + i√3.
    use 1 + I * Real.sqrt 3
    constructor
    · -- Show the real part is non-zero.
      have h1 : (1 + I * Real.sqrt 3 : ℂ).re = 1 := by
        simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, mul_comm]
      intro h
      rw [h1] at h
      norm_num at h
    · -- Show it equals -8.
      have h2 : (1 + I * Real.sqrt 3 : ℂ).re = 1 := by
        simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, mul_comm]
      have h3 : ((1 + I * Real.sqrt 3 : ℂ)^4).re = -8 := by
        simp [pow_two, pow_succ, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_add, mul_comm]
        ring_nf
        <;> norm_num [Real.sqrt_sq]
        <;> nlinarith
      rw [show ((1 + I * Real.sqrt 3 : ℂ) ^ 4).re / (1 + I * Real.sqrt 3 : ℂ).re ^ 4 = ((1 + I * Real.sqrt 3 : ℂ) ^ 4).re / (1 + I * Real.sqrt 3 : ℂ).re ^ 4 by rfl]
      rw [h3, h2]
      all_goals norm_num
  · -- Let x be an element of the set.
    intro x hx
    rcases hx with ⟨z, hzre, hx⟩
    have h1 : (z^4).re = z.re^4 - 6 * z.re^2 * z.im^2 + z.im^4 := by
      simp [pow_two, pow_succ, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_comm, mul_assoc]
      ring_nf
    have h2 : (z^4).re / z.re^4 = 1 - 6 * (z.im^2 / z.re^2) + (z.im^4 / z.re^4) := by
      rw [h1]
      have h3 : z.re ≠ 0 := hzre
      field_simp [h3]
      <;> ring_nf <;> field_simp [h3]
    rw [hx, h2]
    have h3 : (z.im^2 / z.re^2) ≥ 0 := by
      apply div_nonneg
      · -- Show z.im^2 ≥ 0
        nlinarith [sq_nonneg z.im]
      · -- Show z.re^2 ≥ 0
        nlinarith [sq_nonneg z.re, sq_pos_of_ne_zero hzre]
    have h4 : z.im^4 / z.re^4 = (z.im^2 / z.re^2) ^ 2 := by
      have h3a : z.re ≠ 0 := hzre
      field_simp [h3a]
      <;> ring_nf
    rw [h4]
    nlinarith [sq_nonneg ((z.im^2 / z.re^2) - 3), sq_nonneg z.re, sq_nonneg z.im, sq_pos_of_ne_zero hzre]