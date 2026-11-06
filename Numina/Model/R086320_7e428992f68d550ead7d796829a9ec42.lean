import Mathlib

open Real

theorem algebra_314307 {f : ℝ → ℝ} (hf : ∀ x, f x = (x ^ 2 - 100 * x + 196 + abs (x ^ 2 - 100 * x + 196)) / 2)
    (S : Finset ℕ) (hS : S = Finset.Icc 1 100) :
    ∑ x ∈ S, f x = 390 := by 
  rw [hS]
  norm_num [Finset.sum_Icc_succ_top, hf]
  <;> ring_nf <;> norm_num [abs_of_nonneg, abs_of_nonpos] <;> ring_nf <;> norm_num