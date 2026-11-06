import Mathlib

open Polynomial
open Complex

theorem algebra_20392 {a b : ℝ} :
    (X ^ 2 + C 1) ∣ (C a * X + C b) * (X ^ 5 + C 1) - (C 5 * X + C 1) → (a, b) = (2, 3) := by
  intro h
  rcases h with ⟨h3, h4⟩
  have eq1 := congr_arg (fun f : Polynomial ℝ => f.eval₂ (algebraMap ℝ ℂ) (Complex.I)) h4
  simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I] at eq1 
  ring_nf at eq1 
  have eq2 := congr_arg (fun f : Polynomial ℝ => f.eval₂ (algebraMap ℝ ℂ) (-Complex.I)) h4
  simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I] at eq2 
  ring_nf at eq2 
  have h5 : a = 2 := by
    linarith 
  have h6 : b = 3 := by
    linarith 
  simp [Prod.ext_iff, h5, h6]