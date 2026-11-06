import Mathlib

theorem calculus_16669 {v w : Fin 3 → ℝ} (h : crossProduct v w = ![5, -2, 4]) :
    crossProduct (v + w) (v + w) = ![0, 0, 0] := by
  simp [crossProduct, Fin.sum_univ_three, add_mul, mul_add, sub_self, zero_sub]
  <;> ring