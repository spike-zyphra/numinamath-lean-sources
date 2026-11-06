import Mathlib

open Finset Real

theorem algebra_306495 {n : ℕ} :
    ∑ i ∈ range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring_nf
    omega