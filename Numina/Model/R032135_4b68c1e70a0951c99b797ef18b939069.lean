import Mathlib

theorem calculus_12262 {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A = !![0, 1, 2; 1, 0, 1; 2, 1, 0]) :
    {(p, q, r) : ℝ × ℝ × ℝ | A ^ 3 + p • A ^ 2 + q • A + r • 1 = 0} = {(0, -6, -4)} := by
  ext ⟨p, q, r⟩ 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [hA]
  have eq1 : ( !![0, 1, 2; 1, 0, 1; 2, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) ^ 3 = !![4, 6, 12; 6, 4, 6; 12, 6, 4] := by
    simp [pow_succ, Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_three, Fin.sum_univ_three]
    <;> norm_num
  have eq2 : ( !![0, 1, 2; 1, 0, 1; 2, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) ^ 2 = !![5, 2, 1; 2, 2, 2; 1, 2, 5] := by 
    simp [pow_succ, Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_three, Fin.sum_univ_three]
    <;> norm_num
  simp only [eq1, eq2]
  constructor
  · -- Forward direction: the equation implies the values.
    intro h
    have eq3 := congr_arg (λ m => m 0 0) h
    have eq4 := congr_arg (λ m => m 0 1) h
    have eq5 := congr_arg (λ m => m 0 2) h
    have eq6 := congr_arg (λ m => m 1 0) h
    have eq7 := congr_arg (λ m => m 1 1) h
    have eq8 := congr_arg (λ m => m 1 2) h
    have eq9 := congr_arg (λ m => m 2 0) h
    have eq10 := congr_arg (λ m => m 2 1) h
    have eq11 := congr_arg (λ m => m 2 2) h
    simp [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three, pow_two] at eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11
    norm_num at eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11
    have eq12 : p = 0 := by 
      linarith
    have eq13 : q = -6 := by
      linarith 
    have eq14 : r = -4 := by
      linarith 
    simp [eq12, eq13, eq14]
  · -- Backward: values satisfy the equation
    rintro ⟨rfl, rfl, rfl⟩
    ext i j 
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three, pow_two] <;> norm_num