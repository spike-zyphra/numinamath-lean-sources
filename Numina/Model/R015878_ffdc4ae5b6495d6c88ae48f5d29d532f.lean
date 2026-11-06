import Mathlib

open Finset Real

theorem number_theory_56775 : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧
    (∏ i ∈ Icc 2 29, (1 - 1 / ((2 ^ i - 1) : ℚ))) = m / n := by

  use 2 ^ 28
  use 2 ^ 29 - 1
  constructor
  · -- Show that $m > 0$.
    norm_num
  constructor
  · -- Show that $n > 0$.
    norm_num
  constructor
  · -- Show that $Nat.Coprime$.
    norm_num
  · -- Show that the product equals m/n.
    native_decide