import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_308522 (z1 z2 : ℂ) (h₀ : z2 = z1 * I - 2)
  (h₁ : abs (z1 - 2) + abs (z1 + 2) = 10) :
  (z2.re + 2)^2 / 21 + (z2.im)^2 / 25 = 1 := by
  have eq1 : z2.re = -z1.im - 2 := by
    rw [h₀]
    simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    <;> ring_nf
    <;> simp
  have eq2 : z2.im = z1.re := by
    rw [h₀]
    simp [pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    <;> ring_nf
    <;> simp
  have eq3 : abs (z1 - 2) = Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  have eq4 : abs (z1 + 2) = Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  have h2 : (z1.re) ^ 2 / 25 + (z1.im) ^ 2 / 21 = 1 := by
    have h3 : Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2) + Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2) = 10 := by 
      rw [eq3, eq4] at h₁
      exact_mod_cast h₁
    have h4 : (Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2) + Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2)) ^ 2 = 100 := by
      rw [h3]
      norm_num
    have h5 : (Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2) + Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2)) ^ 2 =
          (Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2)) ^ 2 + (Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2)) ^ 2 + 2 * (Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2) * Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2)) := by
      ring
    have h6 : (Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2)) ^ 2 = (z1.re - 2) ^ 2 + z1.im ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h7 : (Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2)) ^ 2 = (z1.re + 2) ^ 2 + z1.im ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h5, h6, h7] at h4
    nlinarith [sq_nonneg (Real.sqrt ((z1.re - 2) ^ 2 + z1.im ^ 2) - Real.sqrt ((z1.re + 2) ^ 2 + z1.im ^ 2)), 
              Real.sqrt_nonneg ((z1.re - 2) ^ 2 + z1.im ^ 2), 
              Real.sqrt_nonneg ((z1.re + 2) ^ 2 + z1.im ^ 2),
              sq_nonneg (z1.re), sq_nonneg (z1.im), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (z1.re - 2) ^ 2 + z1.im ^ 2 by positivity), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (z1.re + 2) ^ 2 + z1.im ^ 2 by positivity)
            ]
  rw [eq1, eq2]
  field_simp at h2 ⊢
  nlinarith