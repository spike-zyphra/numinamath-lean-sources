import Mathlib

open Real

theorem calculus_15715 (a b : ℝ) :
    Matrix.det !![1, cos (a - b), cos a; cos (a - b), 1, cos b; cos a, cos b, 1] = 0 := by
  simp [Matrix.det_fin_three, cos_sub]
  <;> ring_nf
  <;> simp [sin_sq, cos_sq, sub_eq_zero]
  <;> ring_nf
  <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq] <;> ring