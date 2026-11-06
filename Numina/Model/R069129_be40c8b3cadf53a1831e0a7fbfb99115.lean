import Mathlib

open Finset Real

theorem algebra_111747 {f : ℕ → ℝ} (hf : ∀ n, f n = n ^ 2 + 3 * n + 2) :
    ∏ i ∈ range 2019, (1 - 2 / f (i + 1)) = 337 / 1010 := by
  norm_num [hf, prod_range_succ]