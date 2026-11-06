import Mathlib

open Finset

/-How many orderings (a1, a2, a3, a4, a5, a6, a7, a8) of
(1, 2, ..., 8) such that
a1 - a2 + a3 - a4 + a5 - a6 + a7 - a8 = 0 ?-/

theorem combinatorics_609083:
  ((Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8 ×ˢ Icc (1: ℤ) 8).filter
  (fun (a1, a2, a3, a4, a5, a6, a7, a8) => a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧ a1 ≠ a5 ∧ a1 ≠ a6 ∧ a1 ≠ a7 ∧ a1 ≠ a8 ∧
  a2 ≠ a3 ∧ a2 ≠ a4 ∧ a2 ≠ a5 ∧ a2 ≠ a6 ∧ a2 ≠ a7 ∧ a2 ≠ a8 ∧
  a3 ≠ a4 ∧ a3 ≠ a5 ∧ a3 ≠ a6 ∧ a3 ≠ a7 ∧ a3 ≠ a8 ∧
  a4 ≠ a5 ∧ a4 ≠ a6 ∧ a4 ≠ a7 ∧ a4 ≠ a8 ∧
  a5 ≠ a6 ∧ a5 ≠ a7 ∧ a5 ≠ a8 ∧
  a6 ≠ a7 ∧ a6 ≠ a8 ∧
  a7 ≠ a8 ∧ a1 - a2 + a3 - a4 + a5 - a6 + a7 - a8 = 0)).card = 4608 := by

  native_decide