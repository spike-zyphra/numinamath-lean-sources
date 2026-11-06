import Mathlib

theorem calculus_15315 (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A = !![-3, 4, 0; 5, -7, 0; 0, 0, 1]) (hB : A * B = 1) :
    B = !![-7, -4, 0; -5, -3, 0; 0, 0, 1] := by 
  have h1 : B = !![-7, -4, 0; -5, -3, 0; 0, 0, 1] := by 
    have eq1 := congr_arg (fun X => X 0 0) hB
    have eq2 := congr_arg (fun X => X 0 1) hB
    have eq3 := congr_arg (fun X => X 0 2) hB
    have eq4 := congr_arg (fun X => X 1 0) hB
    have eq5 := congr_arg (fun X => X 1 1) hB
    have eq6 := congr_arg (fun X => X 1 2) hB
    have eq7 := congr_arg (fun X => X 2 0) hB
    have eq8 := congr_arg (fun X => X 2 1) hB
    have eq9 := congr_arg (fun X => X 2 2) hB
    simp [hA, Matrix.mul_apply, Fin.sum_univ_three, mul_add, add_mul] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9
    have b00 : B 0 0 = -7 := by
      linarith
    have b01 : B 0 1 = -4 := by
      linarith
    have b02 : B 0 2 = 0 := by
      linarith
    have b10 : B 1 0 = -5 := by
      linarith
    have b11 : B 1 1 = -3 := by
      linarith
    have b12 : B 1 2 = 0 := by
      linarith
    have b20 : B 2 0 = 0 := by
      linarith
    have b21 : B 2 1 = 0 := by
      linarith
    have b22 : B 2 2 = 1 := by
      linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [b00, b01, b02, b10, b11, b12, b20, b21, b22] <;> try { aesop }
    <;> try { tauto }
    all_goals
      try { 
        linarith 
      }
    <;> try { tauto }
  exact h1