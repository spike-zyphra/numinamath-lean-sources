import Mathlib

open Matrix

theorem calculus_16532 : ¬∃ M : Matrix (Fin 2) (Fin 2) ℝ, ∀ a b c d : ℝ,
    M * !![a, b; c, d] = !![2 * a, b; 2 * c, d] := by
  rintro ⟨M, h⟩
  have h1 := h 1 0 0 1
  have h2 := h 0 1 1 0
  have eq1 := congr_arg (fun x => x 0 0) h1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq1 
  have eq2 := congr_arg (fun x => x 0 1) h1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq2 
  have eq3 := congr_arg (fun x => x 1 0) h1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq3 
  have eq4 := congr_arg (fun x => x 1 1) h1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq4 
  have eq5 := congr_arg (fun x => x 0 0) h2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq5 
  have eq6 := congr_arg (fun x => x 0 1) h2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq6 
  linarith