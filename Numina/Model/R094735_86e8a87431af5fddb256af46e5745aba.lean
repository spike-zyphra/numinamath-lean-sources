import Mathlib
open Mathlib

theorem algebra_84
    {f : ℝ → ℝ}
    {a : ℕ → ℝ}
    (hf : ∀ x : ℝ, f x = 1 / 2 * (x ^ 2 - 100 * x + 196 + abs (x ^ 2 - 100 * x + 196))) (ha : ∀ n, a n = f (n : ℝ))
    : ∑ i : Fin 100, a (i + 1) = 390 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ha, hf]
  norm_num [abs_of_nonneg, abs_of_nonpos]
  <;> ring_nf <;> norm_num