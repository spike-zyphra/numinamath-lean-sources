import Mathlib

theorem calculus_22700 {M : Matrix (Fin 2) (Fin 2) ℝ} {e₁ : Matrix (Fin 2) (Fin 1) ℝ} {e₂ : Matrix (Fin 2) (Fin 1) ℝ} (h1 : e₁ = !![1; 0]) (h2 : e₂ = !![0; 1]) (hM : M * e₁ = !![3; 0]) (hM' : M * e₂ = !![2; -7]) :
    M = !![3, 2; 0, -7] := by

  rw [h1] at hM
  rw [h2] at hM'
  have eq1 := congr_arg (fun x => x 0 0) hM
  have eq2 := congr_arg (fun x => x 1 0) hM
  have eq3 := congr_arg (fun x => x 0 0) hM'
  have eq4 := congr_arg (fun x => x 1 0) hM'
  simp [Matrix.mul_apply, Fin.sum_univ_zero, Fin.sum_univ_succ] at eq1 eq2 eq3 eq4
  funext i j
  fin_cases i <;> fin_cases j <;> simp [eq1, eq2, eq3, eq4]
  all_goals linarith