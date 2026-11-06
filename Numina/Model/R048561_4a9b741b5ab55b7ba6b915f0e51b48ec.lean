import Mathlib

open Finset

theorem algebra_219857 {f : ℕ → ℤ} (hf : ∀ x, f x = 2 ^ x + x ^ 2)
    (a : ℕ → ℤ) (ha : ∀ n, ∑ i ∈ range n, a i = f n) :
    ∀ n, a n = if n = 1 then 3 else (if n ≥ 20 then (2 ^ (n - 1) + 2 * n - 1) else 0) := by
  specialize ha 0
  norm_num [hf] at ha
  all_goals linarith