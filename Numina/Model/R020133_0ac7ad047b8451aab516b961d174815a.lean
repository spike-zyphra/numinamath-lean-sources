import Mathlib

open Polynomial

theorem algebra_8432 {a b : ℤ} (p : ℤ[X]) (hp : p = X ^ 2 + C a * X + C b) (n : ℤ) :
    ∃ m : ℤ, (p.eval n) * (p.eval (n + 1)) = p.eval m := by
  use n ^ 2 + (a + 1) * n + b
  have eq1 : p.eval n = n ^ 2 + a * n + b := by
    rw [hp]
    simp [eval_X, eval_add, eval_mul, eval_pow, eval_C]
    <;> ring
  have eq2 : p.eval (n + 1) = (n + 1) ^ 2 + a * (n + 1) + b := by
    rw [hp]
    simp [eval_X, eval_add, eval_mul, eval_pow, eval_C]
    <;> ring
  have eq3 : p.eval (n ^ 2 + (a + 1) * n + b) = (n ^ 2 + (a + 1) * n + b) ^ 2 + a * (n ^ 2 + (a + 1) * n + b) + b := by
    rw [hp]
    simp [eval_X, eval_add, eval_mul, eval_pow, eval_C]
    <;> ring
  rw [eq1, eq2, eq3]
  ring_nf