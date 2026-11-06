import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_322436 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : ∃ z : ℂ, ‖z‖ ≤ 1 ∧ z + (z.1 - z.2 * I) * ‖z‖ = a + b * I) :
  a * b ≤ 1 / 8 := by
  rcases h with ⟨z, hz1, hz⟩
  have h_mod : ‖z‖ = Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, 
        Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, h_mod] at eq1 eq2
  have h1 : (z.1) * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) = a := by linarith
  have h2 : (z.2) * (1 - Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) = b := by linarith
  have h3 : (z.1 ^ 2 + z.2 ^ 2) ≤ (1 : ℝ) := by
    have h_mod_sq : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (1 : ℝ) := by
      linarith [hz1, h_mod]
    have h4 : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 ≤ (1 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ z.1 ^ 2 + z.2 ^ 2 by positivity)]
    have h5 : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 = (z.1 ^ 2 + z.2 ^ 2) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [h_mod_sq, h4, h5]
  have h4 : a * b = z.1 * z.2 * (1 - (z.1 ^ 2 + z.2 ^ 2)) := by
    calc
      a * b = (z.1 * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2))) * (z.2 * (1 - Real.sqrt (z.1 ^ 2 + z.2 ^ 2))) := by
        rw [show a = z.1 * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) by linarith, 
            show b = z.2 * (1 - Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) by linarith]
        all_goals nlinarith
      _ = z.1 * z.2 * ((1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) * (1 - Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ) := by ring
      _ = z.1 * z.2 * (1 - Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 ) := by 
        ring_nf
      _ = z.1 * z.2 * (1 - (z.1 ^ 2 + z.2 ^ 2) ) := by
        have h5 : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h5]
  have h5 : z.1 * z.2 * (1 - (z.1 ^ 2 + z.2 ^ 2)) ≤ 1 / 8 := by
    nlinarith [sq_nonneg (z.1 ^ 2 - 1 / 4), sq_nonneg (z.2 ^ 2 - 1 / 4), sq_nonneg (z.1 * z.2 - 1 / 4), sq_nonneg (z.1 ^ 2 + z.2 ^ 2 - 1 / 2), mul_nonneg (show 0 ≤ z.1 ^ 2 by positivity) (show 0 ≤ z.2 ^ 2 by positivity), sq_nonneg (z.1 - z.2), sq_nonneg (z.1 + z.2), mul_pos ha hb, h3]
  nlinarith [h4, h5]