import Mathlib

open Matrix Real

theorem algebra_154011 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A = !![3, 1, 2; -1, 2, 5; 0, -4, 2]) :
    A.det = 82 := by 
  rw [hA]
  simp only [Matrix.det_fin_three, Matrix.det_fin_two, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_zero]
  dsimp
  simp [sub_eq_add_neg]
  <;> ring