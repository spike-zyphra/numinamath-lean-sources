import Mathlib
open Finset 

-- Generate all 5-tuples of integers from 1 to 5 (inclusive), represented as lists of length 5.
-- This corresponds to the Cartesian product [1,2,3,4,5]^5.
def allTuples : List (List ℕ) :=
  List.range 5 >>= fun a1 =>
  List.range 5 >>= fun a2 =>
  List.range 5 >>= fun a3 =>
  List.range 5 >>= fun a4 =>
  List.range 5 >>= fun a5 =>
    [ [a1 + 1, a2 + 1, a3 + 1, a4 + 1, a5 + 1] ]

-- Determine whether the three numbers a, b, c form an arithmetic progression in any order.
def isAP (a b c : ℕ) : Bool :=
  a + c = 2 * b ∨ b + c = 2 * a ∨ a + b = 2 * c

-- A 5-tuple is perfect if no subset of three distinct elements forms an arithmetic progression.
-- This checks all combinations of 3 elements from the tuple.
def isPerfect (t : List ℕ) : Bool :=
  (t.enum.sublistsLen 3).all (λ l =>
    match l with
    | [(_, a), (_, b), (_, c)] => !isAP a b c
    | _ => true)

-- Evaluate the number of perfect 5-tuples (i.e., tuples that satisfy the isPerfect predicate).
theorem combinatorics_609295: (allTuples.filter isPerfect).length = 780 := by 
  native_decide