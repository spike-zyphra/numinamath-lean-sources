import Mathlib

theorem calculus_23424 {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM₁ : M * (!![2; 1] : Matrix (Fin 2) (Fin 1) ℝ) = !![5; 4])
    (hM₂ : M * (!![3; 0] : Matrix (Fin 2) (Fin 1) ℝ) = !![1; 2]) :
    M.det = -2 := by

  have eq1 := congr_arg (fun x => x 0 0) hM₁
  have eq2 := congr_arg (fun x => x 1 0) hM₁
  have eq3 := congr_arg (fun x => x 0 0) hM₂
  have eq4 := congr_arg (fun x => x 1 0) hM₂

  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul] at eq1 eq2 eq3 eq4

  have ha : M 0 0 = 1 / 3 := by
    linarith

  have hb : M 0 1 = 13 / 3 := by
    linarith

  have hc : M 1 0 = 2 / 3 := by
    linarith

  have hd : M 1 1 = 8 / 3 := by
    linarith

  simp [Matrix.det_fin_two, ha, hb, hc, hd]
  all_goals norm_num