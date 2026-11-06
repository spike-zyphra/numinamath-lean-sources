import Mathlib

open Finset

/-How many sequences of 0 s and 1 s are there of length 10 such that
there are no three 0 s or 1 s consecutively anywhere in the sequence?-/

theorem combinatorics_611023:
 ((Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1).filter
  fun (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) =>
  ¬ ( (x1 = x2 ∧ x2 = x3)
    ∨ (x2 = x3 ∧ x3 = x4)
    ∨ (x3 = x4 ∧ x4 = x5)
    ∨ (x4 = x5 ∧ x5 = x6)
    ∨ (x5 = x6 ∧ x6 = x7)
    ∨ (x6 = x7 ∧ x7 = x8)
    ∨ (x7 = x8 ∧ x8 = x9)
    ∨ (x8 = x9 ∧ x9 = x10) )).card = 178 := by

    native_decide