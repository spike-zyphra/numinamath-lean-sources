import Mathlib

open Polynomial

theorem algebra_9335 {f : Polynomial ℤ} (hf : f = X^6 - 2*X^5 + 3*X^3 + 4*X^2 - 6*X + 5) :
  f.eval 2 = 33 := by 
  rw [hf]
  norm_num [eval_add, eval_mul, eval_pow, eval_X]