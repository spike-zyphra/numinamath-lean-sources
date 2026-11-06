import Mathlib

open Finset Real

theorem algebra_20879 (n : ℕ) (hn : 0 < n) (f : ℕ → ℝ)
    (hf : f = λ n : ℕ => ((2 * n + 2) ^ 4 + (1 : ℝ) / 4) / ((2 * n + 1) ^ 4 + 1 / 4)) :
    ∏ i ∈ Finset.range n, f i = 8 * n ^ 2 + 4 * n + 1 := by
  induction n with
  | zero =>
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      norm_num [hf]
    | succ n =>
      rw [prod_range_succ, ih (by linarith)]
      simp [hf]
      field_simp
      nlinarith [sq_nonneg ( (2 * (n : ℝ) + 1) ^ 2 - (2 * (n : ℝ) + 3) ^ 2 ), sq_nonneg ( (2 * (n : ℝ) + 1) ^ 2 - (2 * (n : ℝ) + 3) ^ 2 + 2 ), sq_nonneg ( (n : ℝ) * (n + 1) ) ]