import Mathlib

theorem calculus_13761 (a b c d : ℝ) (h : Matrix.det (fun i j : Fin 2 => if i = 0 ∧ j = 0 then a else if i = 0 ∧ j = 1 then b else if i = 1 ∧ j = 0 then c else d) = 5) :
    Matrix.det (fun i j : Fin 2 => if i = 0 ∧ j = 0 then 2*a else if i = 0 ∧ j = 1 then 2*b else if i = 1 ∧ j = 0 then 2*c else 2*d) = 20 := by 
  simp [Matrix.det_fin_two, Fin.sum_univ_two, mul_add, add_mul] at h ⊢
  linarith