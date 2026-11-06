import Mathlib

open Finset

/-Determine the number of 8-tuples of nonnegative integers
(a1, a2, a3, a4, b1, b2, b3, b4) satisfying 0 ≤ ak ≤ k, for each
k = 1, 2, 3, 4 and a1 + a2 + a3 + a4 + 2b1 + 3b2 + 4b3 + 5b4 = 19.-/

theorem combinatorics_608296 :
  ((Icc 0 1 ×ˢ Icc 0 2 ×ˢ Icc 0 3 ×ˢ Icc 0 4 ×ˢ Icc 0 10 ×ˢ Icc 0 10 ×ˢ Icc 0 10 ×ˢ Icc 0 10).filter
  (fun (a1, a2, a3, a4, b1, b2, b3, b4) => a1 + a2 + a3 + a4 + 2 * b1 + 3 * b2 + 4 * b3 + 5 * b4 = 19)).card = 1540 := by

    native_decide