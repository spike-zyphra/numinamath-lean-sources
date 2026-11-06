import Mathlib

open Finset

/-Consider a permutation (a1, a2, a3, a4, a5) of {1, 2, 3, 4, 5}.
We say the tuple (a1, a2, a3, a4, a5) is flawless if for all
1 ≤ i < j < k ≤ 5, the sequence (ai, aj, ak) is not an arithmetic
progression (in that order). Find the number of flawless 5-tuples-/

theorem combinatorics_609324:
  ((Icc 1 5 ×ˢ Icc 1 5 ×ˢ Icc 1 5 ×ˢ Icc 1 5 ×ˢ Icc 1 5).filter
  (fun (a1, a2, a3, a4, a5) =>
    (a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧ a1 ≠ a5 ∧ a2 ≠ a3 ∧ a2 ≠ a4 ∧ a2 ≠ a5 ∧
     a3 ≠ a4 ∧ a3 ≠ a5 ∧ a4 ≠ a5) ∧
  ¬ (a1 + a3 = 2 * a2 ∨ a1 + a4 = 2 * a2 ∨ a1 + a5 = 2 * a2 ∨
    a1 + a4 = 2 * a3 ∨ a1 + a5 = 2 * a3 ∨ a1 + a5 = 2 * a4 ∨
    a2 + a4 = 2 * a3 ∨ a2 + a5 = 2 * a3 ∨ a2 + a5 = 2 * a4 ∨
    a3 + a5 = 2 * a4))).card = 20 := by

    native_decide
    