import Mathlib

open Finset

/-Compute the number of ordered quintuples of nonnegative integers
(a1,a2,a3,a4,a5) such that
0 ≤ a1,a2,a3,a4,a5 ≤ 7 and 5 divides
2^a1+ 2^a2 +2^a3 +2^a4 +2^a5.-/

theorem combinatorics_609261: ((Icc 0 7 ×ˢ Icc 0 7 ×ˢ Icc 0 7 ×ˢ Icc 0 7 ×ˢ Icc 0 7).filter
  (fun (a1, a2, a3, a4, a5) => 5 ∣ 2 ^ a1+ 2 ^ a2 + 2 ^ a3 + 2 ^ a4 + 2 ^ a5)).card = 6528 := by

    native_decide