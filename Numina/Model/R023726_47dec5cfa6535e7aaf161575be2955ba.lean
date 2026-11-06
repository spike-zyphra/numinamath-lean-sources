import Mathlib

open Matrix

theorem calculus_12041 : ¬∃ M : Matrix (Fin 2) (Fin 2) ℝ,
    ∀ A : Matrix (Fin 2) (Fin 2) ℝ, M * A = (fun i j => if j = 0 then A i 1 else A i 0) := by
  rintro ⟨M, h⟩
  have h1 := h ( !![1, 0; 0, 0])
  have eq1 := congr_arg (fun X => X 0 0) h1
  have eq2 := congr_arg (fun X => X 0 1) h1
  have eq3 := congr_arg (fun X => X 1 0) h1
  have eq4 := congr_arg (fun X => X 1 1) h1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq1 eq2 eq3 eq4
  all_goals linarith