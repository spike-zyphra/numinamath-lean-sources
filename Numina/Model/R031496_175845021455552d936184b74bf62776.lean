import Mathlib

theorem calculus_14423 {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : ∀ N : Matrix (Fin 3) (Fin 3) ℝ,
      M * N = !![N 1 0, N 1 1, N 1 2; N 0 0, N 0 1, N 0 2; 2 * N 2 0, 2 * N 2 1, 2 * N 2 2]) :
    M = !![0, 1, 0; 1, 0, 0; 0, 0, 2] := by

  have eq1 := hM ( !![1, 0, 0; 0, 1, 0; 0, 0, 1] )
  have eq2 := congr_arg (fun X => X 0 0) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq2
  have eq3 := congr_arg (fun X => X 0 1) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq3
  have eq4 := congr_arg (fun X => X 0 2) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq4
  have eq5 := congr_arg (fun X => X 1 0) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq5
  have eq6 := congr_arg (fun X => X 1 1) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq6
  have eq7 := congr_arg (fun X => X 1 2) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq7
  have eq8 := congr_arg (fun X => X 2 0) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq8
  have eq9 := congr_arg (fun X => X 2 1) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq9
  have eq10 := congr_arg (fun X => X 2 2) eq1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq10
  funext i j
  fin_cases i <;> fin_cases j <;> simp [eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10]