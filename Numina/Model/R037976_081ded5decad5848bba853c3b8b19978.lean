import Mathlib

open Polynomial

theorem algebra_72183 {p q : ℝ} (h : (X^2 + 2*X + 5 : ℝ[X]) ∣ (X^4 + C p * X^2 + C q)) :
    (p, q) = (6, 25) := by
  rcases h with ⟨h1, h2⟩
  have eq1 := congr_arg (fun f => f.eval₂ (algebraMap ℝ ℂ) (Complex.I * 2 - 1 : ℂ)) h2
  simp [pow_two, pow_succ, Complex.ext_iff, mul_add, mul_sub, Complex.I_mul_I] at eq1
  ring_nf at eq1
  have heq1 : p = 6 := by
    norm_num [Complex.ext_iff] at eq1
    nlinarith
  have heq2 : q = 25 := by
    norm_num [Complex.ext_iff] at eq1
    nlinarith [heq1]
  simp [Prod.ext_iff, heq1, heq2]