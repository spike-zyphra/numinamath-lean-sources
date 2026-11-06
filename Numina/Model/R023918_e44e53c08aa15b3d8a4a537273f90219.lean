import Mathlib

theorem calculus_13178 (a b : Fin 3 → ℝ) (h : crossProduct a b = ![5, 4, -7]) :
    crossProduct a (3 • b) = ![15, 12, -21] := by
  have h1 : crossProduct a (3 • b) = 3 • (crossProduct a b) := by
    simp [crossProduct, Fin.sum_univ_succ, mul_add, add_mul, mul_assoc]
    <;> ring
  rw [h1, h]
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero, mul_add, add_mul, mul_comm]
  <;> norm_num