import Mathlib

open Finset Real

theorem algebra_177666 (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Icc 1 n, (i + 2) / ((i * (i + 1) * (i + 3) * (i + 4)) : ℝ) =
    n * (n + 5) / (8 * (n + 1) * (n + 4)) := by
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      norm_num
    | succ n =>
      rw [sum_Icc_succ_top (by linarith)]
      rw [ih (by linarith)]
      field_simp
      ring