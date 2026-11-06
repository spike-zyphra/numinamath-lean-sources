import Mathlib

open Finset

/-Count the number of sequences
 1 ≤ a1 ≤  a2 ≤ a3 ≤ a4 ≤ a5 of integers with ai ≤ i for all i-/

theorem combinatorics_610925: ((Icc 1 1 ×ˢ Icc 1 2 ×ˢ Icc 1 3 ×ˢ Icc 1 4 ×ˢ Icc 1 5).filter
  (fun (x, y, z, w, r) => x ≤ y ∧ y ≤ z ∧ z ≤ w ∧ w ≤ r)).card = 42 := by

  native_decide