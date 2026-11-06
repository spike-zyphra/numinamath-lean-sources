import Mathlib

theorem calculus_23406 {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![1, -2; 1, 4]) (hB : B * A = !![6, 0; 0, 6]) :
    B = !![4, 2; -1, 1] := by
  rw [hA] at hB
  have eq1 := congr_arg (fun x => x 0 0) hB
  have eq2 := congr_arg (fun x => x 0 1) hB
  have eq3 := congr_arg (fun x => x 1 0) hB
  have eq4 := congr_arg (fun x => x 1 1) hB
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul] at eq1 eq2 eq3 eq4
  have eq5 : B 0 0 = 4 := by
    linarith
  have eq6 : B 0 1 = 2 := by
    linarith
  have eq7 : B 1 0 = -1 := by
    linarith
  have eq8 : B 1 1 = 1 := by
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eq5, eq6, eq7, eq8]
  <;> try { linarith }
  all_goals try simp [eq5, eq6, eq7, eq8]