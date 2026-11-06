import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155378 {f : ℝ → ℝ} (hf : f = λ x => sin (4 * x) ^ 2) :
    deriv f = λ x => 4 * sin (8 * x) := by
  rw [hf]
  funext x
  simp [deriv_pow, deriv_mul, deriv_id'', mul_comm]
  <;> field_simp [Real.sin_sq, Real.cos_sq]
  <;> ring_nf <;> simp [Real.sin_two_mul, mul_add, add_mul, mul_assoc]
  <;> ring