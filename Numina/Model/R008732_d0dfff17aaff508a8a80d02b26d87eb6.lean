import Mathlib

open Real

theorem calculus_16339 (y : ℝ) :
    Matrix.det (fun i j : Fin 3 => if i = j then y + 1 else y) = 3 * y + 1 := by
  simp [Matrix.det_fin_three, Fin.sum_univ_three, Fin.sum_univ_two, mul_add, add_mul]
  <;> ring