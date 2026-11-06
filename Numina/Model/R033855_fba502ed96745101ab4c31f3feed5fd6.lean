import Mathlib

open Polynomial

theorem algebra_9145 {p q : ℝ[X]} {m : ℝ} (hp : p = X ^ 2  + C 2 * X - C 2)
    (hq : q = (X + C m) ^ 2 - 3) (hpq : p = q) : m = 1 := by 
  have eq1 := congr_arg (fun f => f.eval 0) hpq
  simp [hp, hq] at eq1 
  have eq2 := congr_arg (fun f => f.eval 1) hpq
  simp [hp, hq] at eq2 
  have eq3 := congr_arg (fun f => f.eval (-1)) hpq
  simp [hp, hq] at eq3
  nlinarith