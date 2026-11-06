import Mathlib

theorem algebra_154052 (X : Fin 3 → ℝ)
    (hX : Matrix.mulVec (fun i j : Fin 3 => if i = 0 ∧ j = 0 then 3 else if i = 0 ∧ j = 1 then -1 else if i = 0 ∧ j = 2 then 0 else if i = 1 ∧ j = 0 then -2 else if i = 1 ∧ j = 1 then 1 else if i = 1 ∧ j = 2 then 1 else if i = 2 ∧ j = 0 then 2 else if i = 2 ∧ j = 1 then -1 else 4) X = ![5, 0, 15]) :
    X = ![2, 1, 3] := by
  have eq1 := congr_arg (λ v => v 0) hX
  have eq2 := congr_arg (λ v => v 1) hX
  have eq3 := congr_arg (λ v => v 2) hX
  simp [Matrix.mulVec, Fin.sum_univ_three] at eq1 eq2 eq3
  have h1 : X 0 = 2 := by
    linarith 
  have h2 : X 1 = 1 := by
    linarith
  have h3 : X 2 = 3 := by
    linarith 
  funext i
  fin_cases i 
  · exact h1
  · exact h2
  · exact h3