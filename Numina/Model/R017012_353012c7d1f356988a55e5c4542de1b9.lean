import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_146003 {z : ℂ} (hz : z = -1 - I * Real.sqrt 3) :
    z = 2 * (Real.cos (-2 * π / 3) + I * Real.sin (-2 * π / 3)) := by 
  rw [hz]
  have h1 : Real.cos (-2 * π / 3) = -1 / 2 := by
    have h1 : Real.cos (-2 * π / 3) = Real.cos (2 * π / 3 : ℝ) := by 
      have : -2 * π / 3 = - (2 * π / 3 : ℝ) := by ring
      rw [this]
      rw [Real.cos_neg]
    rw [h1]
    have h2 : Real.cos (2 * π / 3 : ℝ) = -1 / 2 := by 
      have : 2 * π / 3 = π - π / 3 := by ring
      rw [this]
      rw [Real.cos_pi_sub]
      norm_num
    exact h2
  have h2 : Real.sin (-2 * π / 3) = -Real.sqrt 3 / 2 := by 
    have h3 : Real.sin (-2 * π / 3 : ℝ) = - Real.sin (2 * π / 3 : ℝ) := by 
      have : -2 * π / 3 = - (2 * π / 3 : ℝ) := by ring
      rw [this]
      rw [Real.sin_neg]
    have h4 : Real.sin (2 * π / 3 : ℝ) = Real.sqrt 3 / 2 := by 
      have h1 : Real.sin (2 * π / 3 : ℝ) = Real.sqrt 3 / 2 := by
        have : 2 * π / 3 = π - π / 3 := by ring
        rw [this]
        rw [Real.sin_pi_sub]
        have h2 : Real.sin (π / 3 : ℝ) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        linarith
      exact h1
    rw [h3, h4]
    all_goals ring
  rw [h1, h2]
  simp [Complex.ext_iff, mul_add, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm, mul_assoc]
  all_goals ring_nf <;> norm_num