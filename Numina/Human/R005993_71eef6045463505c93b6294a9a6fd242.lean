import Mathlib

open Finset

/-How many triples (A,B,C) of positive integers (positive integers are the numbers (1,2,3,4,… )
are there such that A+B+C=10, where order does not matter (for instance the triples (2,3,5) and
(3,2,5) are considered to be the same triple) and where two of the integers in a triple could be the same
(for instance (3,3,4) is a valid triple).-/

theorem combinatorics_610991:
  ((Icc 1 10 ×ˢ Icc 1 10 ×ˢ Icc 1 10).filter (fun (A, B, C) => A ≤ B ∧ B ≤ C ∧ A + B + C = 10)).card = 8 := by

    native_decide