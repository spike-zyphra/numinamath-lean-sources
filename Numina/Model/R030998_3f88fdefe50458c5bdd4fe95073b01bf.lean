import Mathlib

open Matrix

theorem calculus_22245 (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P = !![0, 0; 0, 1]) :
    ∀ v : Fin 2 → ℝ, P * !![v 0; v 1] = !![0; v 1] := by
  intro v
  rw [hP]
  simp [mul_apply, Matrix.mul_apply, Fin.sum_univ_two, add_zero, zero_add, mul_zero, zero_mul, mul_one]
  all_goals aesop