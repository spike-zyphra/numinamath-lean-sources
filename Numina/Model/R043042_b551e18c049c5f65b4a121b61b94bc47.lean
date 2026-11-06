import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_18646 (θ : ℝ) (x : ℝ) :
  Matrix.det !![x, sin θ, cos θ; -sin θ, -x, 1; cos θ, 1, x] = -x^3 := by
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring