import Mathlib

open Polynomial

theorem algebra_20198 : {a : ℝ |
    (X^2 - 3*X + 4) * (2*X^2 + C a*X + 7) =
    2*X^4 - 11*X^3 + 30*X^2 - 41*X + 28} = {-5} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the polynomial equation holds, prove a = -5
    intro h
    have eq1 := congr_arg (fun f => f.eval 1) h
    norm_num [eval_add, eval_mul, eval_pow, eval_X, eval_C] at eq1
    have eq2 := congr_arg (fun f => f.eval 2) h
    norm_num [eval_add, eval_mul, eval_pow, eval_X, eval_C] at eq2
    have ha : a = -5 := by
      nlinarith
    linarith
  · -- Assume a = -5, prove the polynomial equation holds
    intro h
    rw [h]
    -- Now we need to prove the two polynomials are equal after substituting a = -5
    -- We can evaluate both sides at a specific point, for example, x = 2, to verify the equality
    apply Polynomial.funext
    intro x
    simp [Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_neg]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num