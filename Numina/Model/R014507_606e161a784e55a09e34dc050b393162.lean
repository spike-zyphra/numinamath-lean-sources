import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_196842 :
  IsLeast {x : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ x = (‖z - 4‖^2) + (‖z + 3 * I‖^2)} 17 := by
  constructor
  · -- Show 17 is in the set
    use 4 / 5 - 3 / 5 * I
    constructor
    · -- Show the norm is 1
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf <;> norm_num
    · -- Show the value is 17
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.I_mul_I]
      all_goals field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf <;> norm_num
  · -- Show the minimality of 17
    intro x hx
    rcases hx with ⟨z, hz, hx⟩
    have h1 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    have h2 : ‖z - 4‖ = Real.sqrt ((z.re - 4) ^ 2 + (z.im) ^ 2) := by 
      have h1' : ‖z - 4‖ = Real.sqrt ((z - 4).re ^ 2 + (z - 4).im ^ 2) := by 
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h1']
      simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, 
        Complex.I_re, Complex.I_im]
      all_goals try ring_nf
    have h3 : ‖z + 3 * I‖ = Real.sqrt ((z.re) ^ 2 + (z.im + 3) ^ 2) := by 
      have h1' : ‖z + 3 * I‖ = Real.sqrt ((z + 3 * I).re ^ 2 + (z + 3 * I).im ^ 2) := by 
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h1']
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, 
        Complex.I_re, Complex.I_im]
      all_goals try ring_nf
    have h4 : ‖z - 4‖^2 = (z.re - 4) ^ 2 + (z.im) ^ 2 := by 
      rw [h2]
      rw [Real.sq_sqrt]
      positivity
    have h5 : ‖z + 3 * I‖^2 = (z.re) ^ 2 + (z.im + 3) ^ 2 := by 
      rw [h3]
      rw [Real.sq_sqrt]
      positivity
    have h6 : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h7 : ‖z‖ = 1 := hz
      rw [h1] at h7
      have h8 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := h7
      have h9 : z.re ^ 2 + z.im ^ 2 = (1 : ℝ) := by
        calc
          z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by 
            rw [Real.sq_sqrt]
            positivity
          _ = (1 : ℝ) ^ 2 := by rw [h8]
          _ = (1 : ℝ) := by norm_num
      exact h9
    rw [hx, h4, h5]
    nlinarith [sq_nonneg (z.re - 4 / 5), sq_nonneg (z.im + 3 / 5), sq_nonneg (z.re), sq_nonneg (z.im)]