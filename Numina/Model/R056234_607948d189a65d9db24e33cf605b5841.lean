import Mathlib

open Matrix Real

theorem calculus_12138 {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R = !![cos (58 * π / 180), -sin (58 * π / 180); sin (58 * π / 180), cos (58 * π / 180)]) :
    R.det = 1 := by 
  rw [hR]
  simp [Matrix.det_fin_two]
  <;> ring_nf <;> simp [Real.cos_sq, Real.sin_sq]
  <;> ring