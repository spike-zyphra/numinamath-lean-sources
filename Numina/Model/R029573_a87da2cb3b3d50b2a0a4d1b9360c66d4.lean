import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_153314 (f : ℝ → ℝ) (hf : f = λ x => 5 * cos x)
  (g : ℝ → ℝ) (hg : g = λ x => cos x) :
  ∫ x in (0)..(Real.pi / 2), π * (f x)^2 - π * (g x)^2 = 6 * π^2 := by 
  rw [hf, hg]
  simp [intervalIntegral.integral_const, mul_pow]
  ring_nf
  <;> field_simp
  <;> ring_nf
  <;> norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
  <;> ring_nf <;> norm_num [mul_add, mul_assoc]
  <;> ring_nf <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> norm_num
  <;> linarith