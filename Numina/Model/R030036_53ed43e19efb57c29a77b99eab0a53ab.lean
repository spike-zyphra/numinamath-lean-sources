import Mathlib

open Polynomial

theorem algebra_282891 : (X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 + X ^ 3 - 1 : Polynomial ℝ) / (X ^ 6 - X ^ 4 + X - 1) = X ^ 2 + X + 1 := by 
  have eq : (X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 + X ^ 3 - 1 : Polynomial ℝ) = (X^ 2 + X + 1) * (X ^ 6 - X ^ 4 + X - 1) := by 
    ring 
  rw [eq]
  have h2 : (X ^ 6 - X ^ 4 + X - 1 : Polynomial ℝ) ≠ 0 := by
    by_contra h 
    have h3 : (X ^ 6 - X ^ 4 + X - 1 : Polynomial ℝ) = 0 := by 
      simpa using h 
    have eq2 : (X ^ 6 - X ^ 4 + X - 1 : Polynomial ℝ) = X ^ 6 + (-X ^ 4) + X + (-1) := by
      ring 
    rw [eq2] at h3
    have eq3 := congr_arg (fun f => f.eval (1 : ℝ)) h3
    have eq4 := congr_arg (fun f => f.eval (2 : ℝ)) h3
    have eq5 := congr_arg (fun f => f.eval (0 : ℝ)) h3
    simp [pow_two, pow_succ, Polynomial.ext_iff, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at eq3 eq4 eq5 
    all_goals try nlinarith 
  field_simp [h2]