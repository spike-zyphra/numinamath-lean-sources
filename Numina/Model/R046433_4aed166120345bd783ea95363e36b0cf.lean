import Mathlib

open Polynomial

theorem algebra_16775 {P Q : ℂ} (h : (X^2 + C 2 * X + C 5 : Polynomial ℂ) ∣ (X^4 + C P * X^2 + C Q)) :
    P + Q = 31 := by
  rcases h with ⟨h2, heq⟩
  have eq1 := congr_arg (fun f => f.eval (-1 + 2 * Complex.I)) heq
  simp [pow_two, pow_succ, Complex.ext_iff] at eq1 
  have eq2 := congr_arg (fun f => f.eval (-1 - 2 * Complex.I)) heq
  simp [pow_two, pow_succ, Complex.ext_iff] at eq2 
  norm_num [Complex.ext_iff] at eq1 eq2 ⊢
  constructor
  · nlinarith
  · nlinarith