import Mathlib

open Polynomial

theorem algebra_10695 {c p q : ℝ} (h : (6 : ℝ) • X ^ 2 - 4 * X + 12 = c •  (X + C p) ^ 2 + C q) :
  q / p = -34 := by
  have eq1 := congr_arg (fun f => f.eval 0) h
  simp at eq1 
  have eq2 := congr_arg (fun f => f.eval 1) h
  simp at eq2
  have eq3 := congr_arg (fun f => f.eval 2) h
  simp at eq3
  have h1 : c = 6 := by
    nlinarith 
  have hp : p = -1 / 3 := by
    rw [h1] at eq1 eq2 
    nlinarith
  have hq : q = 34 / 3 := by 
    rw [h1, hp] at eq1 
    linarith
  rw [hq, hp]
  norm_num