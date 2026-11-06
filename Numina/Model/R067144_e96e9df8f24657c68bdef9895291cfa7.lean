import Mathlib

open Finset Real

theorem algebra_306850 {f : ℝ → ℝ} (hf : ∀ x, f x = x^5 - 3 * x^3 + 2 * x^2 + 3 * x + 6)
    (A : ℕ → ℝ) (hA : ∀ n, A n = ∏ k ∈ Icc 1 n, ((4 * k - 3) * f (4 * k - 3)) / ((4 * k - 1) * f (4 * k - 1))) :
    A 25 = 1 / 1000001 := by 
  rw [hA 25]
  norm_num [prod_Icc_succ_top, hf]
  <;> linarith