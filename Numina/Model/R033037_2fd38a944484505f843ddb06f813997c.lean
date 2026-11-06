import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_184682 {f : ℝ → ℝ} (hf : f = λ x => cos x * sin (2 * x)) :
    ¬ ∃ x, f x = 7 / 9 := by 
  rintro ⟨x, hx⟩
  have h1 : f x = cos x * sin (2 * x) := by 
    rw [hf]
  rw [h1] at hx
  have h2 : sin (2 * x) = 2 * sin x * cos x := by 
    rw [sin_two_mul]
  rw [h2] at hx
  have h5 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (sin x * cos x), sq_nonneg (sin x ^ 2 - 1 / 3), sq_nonneg (cos x ^ 2 - 2 / 3), sq_nonneg (sin x * cos x), sq_nonneg (sin x - 0), sq_nonneg (cos x - 0), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x * cos x * cos x), sq_nonneg ((7 / 9) - 2 * sin x * cos x * cos x), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x - Real.sqrt 3 / 3), sq_nonneg (sin x + Real.sqrt 3 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3) ]