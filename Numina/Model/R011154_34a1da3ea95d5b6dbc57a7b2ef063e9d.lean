import Mathlib

open Polynomial

theorem algebra_15725 {f : Polynomial ℝ} (hf : f = -2 * (X ^ 7 - X ^ 4 + 3 * X ^ 2 - 5) + 4 * (X ^ 3 + 2 * X) - 3 * (X ^ 5 - 4)) :
  ∑ i in f.support, f.coeff i = 25 := by
  have h1 : ∑ i in f.support, f.coeff i = f.eval 1 := by
    rw [Polynomial.eval_eq_sum]
    <;> simp
    <;> try norm_num
    <;> try tauto
    <;> try linarith
  rw [h1, hf]
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  <;> norm_num