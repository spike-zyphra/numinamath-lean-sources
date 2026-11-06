import Mathlib

open Matrix

theorem calculus_16787 {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M = !![2, 0; 1, -3]) :
    {(a, b) : ℝ × ℝ | M⁻¹ = a • M + b • 1} = {(1 / 6, 1 / 6)} := by
  rw [hM]
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume $\begin{pmatrix} 2 & 0 \\ 1 & -3 \end{pmatrix}^{-1} = a \cdot \begin{pmatrix} 2 & 0 \\ 1 & -3 \end{pmatrix} + b \cdot \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$, prove $(a, b) = (1/6, 1/6)$
    intro h
    have eq1 := congr_arg (fun X => X 0 0) h
    have eq2 := congr_arg (fun X => X 0 1) h
    have eq3 := congr_arg (fun X => X 1 0) h
    have eq4 := congr_arg (fun X => X 1 1) h
    have eq1' : ( !![2, 0; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ )⁻¹ 0 0 = (1 / 2 : ℝ) := by 
      simp [Matrix.inv, Matrix.det, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
      all_goals norm_num
    have eq2' : ( !![2, 0; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ )⁻¹ 0 1 = (0 : ℝ) := by 
      simp [Matrix.inv, Matrix.det, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
      all_goals norm_num
    have eq3' : ( !![2, 0; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ )⁻¹ 1 0 = (1 / 6 : ℝ) := by
      simp [Matrix.inv, Matrix.det, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
      all_goals norm_num
    have eq4' : ( !![2, 0; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ )⁻¹ 1 1 = (-(1 / 3) : ℝ) := by 
      simp [Matrix.inv, Matrix.det, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
      all_goals norm_num
    simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq1 eq2 eq3 eq4 
    norm_num [eq1', eq2', eq3', eq4'] at eq1 eq2 eq3 eq4 
    have ha : a = 1 / 6 := by linarith 
    have hb : b = 1 / 6 := by linarith 
    simp [Prod.ext_iff, ha, hb]
  · -- Show that (1/6, 1/6) works
    rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] 
    all_goals norm_num [Matrix.inv, Matrix.det, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]