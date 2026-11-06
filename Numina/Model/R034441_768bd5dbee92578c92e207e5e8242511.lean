import Mathlib

theorem calculus_23326
    (a b c : Fin 3 → ℝ)
    (h₀ : crossProduct a b = ![6, -7, 3])
    (h₁ : crossProduct a c = ![4, 7, 2])
    (h₂ : crossProduct b c = ![1, -7, 18]) :
    crossProduct (2 * b - a) (3 * c + a) = ![-18, -49, 96] := by 
  have heq1 := congr_arg (fun x => x 0) h₀
  have heq2 := congr_arg (fun x => x 1) h₀
  have heq3 := congr_arg (fun x => x 2) h₀
  have heq4 := congr_arg (fun x => x 0) h₁
  have heq5 := congr_arg (fun x => x 1) h₁
  have heq6 := congr_arg (fun x => x 2) h₁
  have heq7 := congr_arg (fun x => x 0) h₂
  have heq8 := congr_arg (fun x => x 1) h₂
  have heq9 := congr_arg (fun x => x 2) h₂
  simp [crossProduct, Fin.sum_univ_three, Fin.sum_univ_two] at heq1 heq2 heq3 heq4 heq5 heq6 heq7 heq8 heq9
  ext i 
  fin_cases i 
  · -- i = 0
    simp [crossProduct, Fin.sum_univ_three, Fin.sum_univ_two]
    all_goals 
      linarith
  · -- i = 1
    simp [crossProduct, Fin.sum_univ_three, Fin.sum_univ_two]
    all_goals
      linarith
  · -- i = 2
    simp [crossProduct, Fin.sum_univ_three, Fin.sum_univ_two]
    all_goals
      linarith