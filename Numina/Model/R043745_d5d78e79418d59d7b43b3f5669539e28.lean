import Mathlib

/- We use `number_of_blocks` to count the number of blocks of consecutive 1's in the binary expansion of a number. -/
def number_of_blocks : List ℕ → ℕ
| [] => 0 -- The empty list has no blocks.
| [1] => 1 -- A single 1 has one block.
| 1 :: 1 :: t => number_of_blocks (1 :: t) -- If the list starts with at least two 1's, we can remove the first one.
| 1 :: _ :: t => 1 + number_of_blocks t -- If the list starts with one 1 and then one 0, we count one block and then remove the first two elements.
| _ :: t => number_of_blocks t -- Otherwise (the list starts with one 0), we can remove the first element.

theorem number_theory_609368 :
    ∑ i ∈ Finset.Icc 1 256, number_of_blocks (Nat.digits 2 i) = 577 := by 
  native_decide