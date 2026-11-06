import Mathlib

theorem algebra_10629 {f : Polynomial ℤ} (hf : f = 3 * (3 * Polynomial.X ^ 7 + 8 * Polynomial.X ^ 4 - 7) + 7 * (Polynomial.X ^ 5 - 7 * Polynomial.X ^ 2 + 5)) :
    f.eval 1 = 5 := by 
  rw [hf]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  <;> norm_num
  <;> rfl