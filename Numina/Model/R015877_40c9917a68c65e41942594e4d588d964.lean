import Mathlib

open Finset

theorem algebra_234145 {n : ℕ} (hn : 1 < n) :
    ∃ i j, 1 / n = ∑ k ∈ Icc i j, 1 / (k * (k + 1)) := by
  use 2, 1
  simp
  all_goals omega