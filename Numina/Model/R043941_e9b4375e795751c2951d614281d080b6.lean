import Mathlib
open Polynomial

theorem algebra_23847 {p : Polynomial ℤ} (hp : p.degree = 3)
    (hmonic : p.coeff 3 = 1) (r s : ℤ)
    (hroots : p = (X - C r) * (X - C s) * (X - C (r * s))) :
    p.eval 1 + p.eval (-1) - 2 * (1 + p.eval 0) ∣ 2 * p.eval (-1) := by 
  rw [hroots]
  use (1 + r * s)
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  <;> ring