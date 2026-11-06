import Mathlib

open Polynomial

theorem algebra_98035 (p q : ℝ) (h : (X^2 + C 2 * X + C 5) ∣ (X^4 + C p * X^2 + C q)) :
    p = 6 ∧ q = 25 := by
  rcases h with ⟨A, hA⟩
  have eq1 := congr_arg (fun f => f.eval₂ (algebraMap ℝ ℂ) (-1 + 2 * Complex.I)) hA
  have eq2 := congr_arg (fun f => f.eval₂ (algebraMap ℝ ℂ) (-1 - 2 * Complex.I)) hA
  simp [pow_two, pow_succ, Complex.ext_iff, eval₂_mul, eval₂_add, eval₂_pow, eval₂_C, Complex.I_sq, mul_add, mul_assoc] at eq1 eq2 
  ring_nf at eq1 eq2
  norm_num [Complex.I_sq, mul_add, mul_assoc] at eq1 eq2
  have ht1 : p = 6 := by
    linarith [eq1, eq2]
  have ht2 : q = 25 := by
    linarith [eq1, eq2]
  exact ⟨ht1, ht2⟩