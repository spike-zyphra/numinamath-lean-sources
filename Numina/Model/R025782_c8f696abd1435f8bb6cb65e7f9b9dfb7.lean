import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_242369 {z : ℂ} (hz : z = 3 - Real.sqrt 3 * .I) :
    z * (Complex.exp (-Real.pi / 3 * .I)) = -2 * Real.sqrt 3 * .I := by 
  rw [hz]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have h1 : Real.cos (-Real.pi / 3) = 1 / 2 := by 
    have h1 : Real.cos (-Real.pi / 3) = Real.cos (Real.pi / 3) := by 
      have h2 : -Real.pi / 3 = - (Real.pi / 3) := by 
        ring
      rw [h2]
      rw [Real.cos_neg]
    rw [h1]
    have h2 : Real.cos (Real.pi / 3) = 1 / 2 := by 
      exact Real.cos_pi_div_three
    linarith
  have h2 : Real.sin (-Real.pi / 3) = -Real.sqrt 3 / 2 := by 
    have h1 : Real.sin (-Real.pi / 3) = - Real.sin (Real.pi / 3) := by
      have h2 : -Real.pi / 3 = - (Real.pi / 3) := by 
        ring
      rw [h2]
      rw [Real.sin_neg]
    have h2' : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      exact Real.sin_pi_div_three
    rw [h1, h2']
    <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num
  simp [h1, h2]
  <;> ring_nf
  <;> field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> field_simp
  <;> ring_nf <;> norm_num
  all_goals ring_nf <;> field_simp <;> ring_nf <;> norm_num
  all_goals tauto