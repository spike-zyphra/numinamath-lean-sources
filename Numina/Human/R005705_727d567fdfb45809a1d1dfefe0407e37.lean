import Mathlib

open Finset

/-
Define the arithmetic function φ!(n) as the product of all integers from 1 to n that are coprime with n. This is also known as the "reduced factorial" or "totient product" function.
-/
def fact (n : ℕ) := ∏ m ∈ (Icc 1 n).filter (fun x => Nat.Coprime x n), m

/-
Theorem: Count the number of integers n in the range [2, 50] such that n divides φ!(n) + 1. The result is 30. This theorem verifies a number theory result: Numbers n for which n divides φ!(n) + 1 are those that have a primitive root.
-/
theorem number_theory_609502 :
    {n ∈ Icc 2 50 | n ∣ fact n + 1}.card = 30 := by 
  rfl

    