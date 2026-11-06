import Mathlib

open Matrix

theorem calculus_23429 (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : ∀ v : Matrix (Fin 3) (Fin 1) ℝ, R * v = (fun i j => if i = 2 then -v i j else v i j)) :
    R = !![1, 0, 0; 0, 1, 0; 0, 0, -1] := by

  have eq1 := hR ( !![1; 0; 0] )
  have eq2 := hR ( !![0; 1; 0] )
  have eq3 := hR ( !![0; 0; 1] )

  have eq11 := congr_arg (fun M => M 0 0) eq1
  have eq12 := congr_arg (fun M => M 1 0) eq1
  have eq13 := congr_arg (fun M => M 2 0) eq1

  have eq21 := congr_arg (fun M => M 0 0) eq2
  have eq22 := congr_arg (fun M => M 1 0) eq2
  have eq23 := congr_arg (fun M => M 2 0) eq2

  have eq31 := congr_arg (fun M => M 0 0) eq3
  have eq32 := congr_arg (fun M => M 1 0) eq3
  have eq33 := congr_arg (fun M => M 2 0) eq3

  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq11 eq12 eq13 eq21 eq22 eq23 eq31 eq32 eq33

  ext i j
  fin_cases i <;> fin_cases j <;> simp [eq11, eq12, eq13, eq21, eq22, eq23, eq31, eq32, eq33]