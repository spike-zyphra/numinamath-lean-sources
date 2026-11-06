import Mathlib
open Polynomial

theorem algebra_2648 (k : ℝ) (h : (X + 1) ∣ X^3 + 3*X^2 - 3*X + C k) : k = -5 := by 
  rcases h with ⟨q, hq⟩
  have h_subst : (X ^ 3 + 3 * X ^ 2 - 3 * X + C k).eval (-1 : ℝ) = 0 := by
    rw [hq]
    simp [eval_mul, eval_add, eval_pow, eval_X, eval_C]
    <;> norm_num at *
    <;> tauto
  simp [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h_subst
  <;> norm_num at h_subst 
  <;> linarith -- Solves linear arithmetic goals