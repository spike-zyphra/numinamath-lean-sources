import Mathlib

theorem algebra_154029 {P : Polynomial ℝ} (hP : ∀ x, P.eval (x + 1) = P.eval x + 2 * x + 1) :
    ∃ c, P = X ^ 2 + c := by
  use (P - X ^ 2)
  apply Polynomial.funext 
  intro x
  have eq4 : P.eval x = P.eval x := by rfl 
  have eq5 : (X ^ 2 + (P - X^2) : Polynomial ℝ).eval x = P.eval x := by 
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  simpa [eq5] using eq4