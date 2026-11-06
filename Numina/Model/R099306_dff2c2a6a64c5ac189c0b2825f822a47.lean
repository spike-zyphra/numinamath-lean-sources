import Mathlib

theorem algebra_187650 : ¬ ∃ P Q : MvPolynomial (Fin 2) ℝ, ∀ x y : ℝ, (x + y) * MvPolynomial.eval (fun n => if n = 0 then x else y) P + (2 * x - y - 3) * MvPolynomial.eval (fun n => if n = 0 then x else y) Q = x ^ 2 + y ^ 2 := by
  rintro ⟨P, Q, h_eq⟩
  have h1 := h_eq 1 (-1)
  norm_num [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X] at h1