import Mathlib

open Finset Real

/-fd the first digit after the decimal point-/
theorem algebra_269395 : (Nat.floor (∑ i ∈ range 1004, (-1 : ℝ)^i / ((2 * i + 1) * (2 * i + 2)) * 10)) % 10 = 4 := by
  have h1 : Nat.floor (∑ i ∈ range 1004, (-1 : ℝ)^i / ((2 * i + 1) * (2 * i + 2)) * 10) = 4 := by
    norm_num [Finset.sum_range_succ, Nat.floor_eq_iff]
  rw [h1]
  all_goals norm_num