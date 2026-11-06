import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_108354 :
  IsGreatest {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖z^2 - z + 2‖} 4 := by 
  constructor
  · -- Show that 4 is in the set.
    use -1
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  · -- Show that 4 is greatest
    intro x h
    rcases h with ⟨z, hz, hx⟩
    have h : ‖z‖ = 1 := hz
    have h1 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h1] at h 
    have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by 
      rw [Real.sqrt_eq_one] at h 
      linarith 
    have h3 : ‖z ^ 2 - z + 2‖ = Real.sqrt ((z ^ 2 - z + 2).re ^ 2 + (z ^ 2 - z + 2).im ^ 2) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h3] at hx 
    have h4 : (z ^ 2 - z + 2).re ^ 2 + (z ^ 2 - z + 2).im ^ 2 ≤ (16 : ℝ) := by
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.ofReal_re, Complex.ofReal_im, sub_eq_add_neg]
      nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im), sq_nonneg (2 * z.re - z.im), sq_nonneg (z.re - 3 / 8), sq_nonneg (z.im), sq_nonneg (z.re - z.im)]
    have h5 : Real.sqrt ((z ^ 2 - z + 2).re ^ 2 + (z ^ 2 - z + 2).im ^ 2) ≤ 4 := by 
      have h8 : Real.sqrt ((z ^ 2 - z + 2).re ^ 2 + (z ^ 2 - z + 2).im ^ 2) ≤ Real.sqrt (16 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h9 : Real.sqrt ((16 : ℝ) ) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      linarith [h8, h9] 
    linarith [h5, hx]