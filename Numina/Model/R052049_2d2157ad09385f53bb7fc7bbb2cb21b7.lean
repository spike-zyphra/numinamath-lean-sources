import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_153296 (f g : ℝ → ℝ)
  (hf : f = λ x => 3 * sin x) (hg : g = λ x => sin x)
  (a b : ℝ) (ha : a = 0) (hb : b = Real.pi) :
  ∫ x in (a)..b, π * (f x)^2 - π * (g x)^2 = 4 * π^2 := by
    rw [ha, hb, hf, hg]
    simp [intervalIntegral.integral_const, mul_comm]
    ring_nf
    <;> field_simp
    <;> ring_nf
    <;> simp [Real.sin_pi, Real.cos_pi, Real.sin_two_mul, Real.cos_two_mul]
    <;> ring