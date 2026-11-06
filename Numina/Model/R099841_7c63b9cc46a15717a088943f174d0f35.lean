import Mathlib

open Finset

theorem number_theory_243753 {a : ℕ → ℕ}
    (ha : ∀ n, a n = ∑ i ∈ range (3 ^ n), 10 ^ i) :
    3 ∣ a 1 ∧ ¬9 ∣ a 1 ∧
    9 ∣ a 2 ∧ ¬27 ∣ a 2 ∧
    27 ∣ a 3 ∧ ¬81 ∣ a 3 := by
  constructor
  · -- Show that 3 divides a 1
    rw [ha 1]
    norm_num [Finset.sum_range_succ]
  constructor
  · -- Show that 9 does not divide a 1
    rw [ha 1]
    norm_num [Finset.sum_range_succ]
  constructor
  · -- Show that 9 divides a 2
    rw [ha 2]
    norm_num [Finset.sum_range_succ]
  constructor
  · -- Show that 27 does not divide a 2
    rw [ha 2]
    norm_num [Finset.sum_range_succ]
  constructor
  · -- Show that 27 divides a 3
    rw [ha 3]
    norm_num [Finset.sum_range_succ]
  · -- Show that 81 does not divide a 3
    rw [ha 3]
    norm_num [Finset.sum_range_succ]