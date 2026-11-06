import Mathlib

open Matrix Real

theorem calculus_11996 : Matrix.det (fun i j : Fin 3 => cos (i * 3 + j + 1)) = 0 := by
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  <;> simp [cos_add, sin_add, cos_two_mul, sin_two_mul] at *
  <;> ring_nf <;> simp [sin_sq, cos_sq] at *
  <;> ring