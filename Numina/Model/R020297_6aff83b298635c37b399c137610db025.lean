import Mathlib

open Matrix

theorem calculus_22846 {P : Matrix (Fin 3) (Fin 3) ℝ}
    (hP : ∀ v : Matrix (Fin 3) (Fin 1) ℝ,
      P * v = (fun i j => if i = 0 then 0 else v i j)) :
    P = !![0, 0, 0; 0, 1, 0; 0, 0, 1] := by
  have eq1 := hP (fun i j =>
    if i = 0 then (1 : ℝ) else if i = 1 then (0 : ℝ) else (0 : ℝ)
  )
  have eq2 := hP (fun i j =>
    if i = 0 then (0 : ℝ) else if i = 1 then (1 : ℝ) else (0 : ℝ)
  )
  have eq3 := hP (fun i j =>
    if i = 0 then (0 : ℝ) else if i = 1 then (0 : ℝ) else (1 : ℝ)
  )
  have eq11 := congr_arg (fun x => x 0 0) (eq1)
  have eq12 := congr_arg (fun x => x 1 0) (eq1)
  have eq13 := congr_arg (fun x => x 2 0) (eq1)
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.one_apply] at eq11 eq12 eq13
  have eq21 := congr_arg (fun x => x 0 0) (eq2)
  have eq22 := congr_arg (fun x => x 1 0) (eq2)
  have eq23 := congr_arg (fun x => x 2 0) (eq2)
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.one_apply] at eq21 eq22 eq23
  have eq31 := congr_arg (fun x => x 0 0) (eq3)
  have eq32 := congr_arg (fun x => x 1 0) (eq3)
  have eq33 := congr_arg (fun x => x 2 0) (eq3)
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.one_apply] at eq31 eq32 eq33
  funext i j
  fin_cases i <;> fin_cases j <;> simp [eq11, eq12, eq13, eq21, eq22, eq23, eq31, eq32, eq33] <;> all_goals linarith