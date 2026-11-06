import Mathlib

open Finset

/-
Problem :
An 8×8 grid of numbers where:
(1) The first row and first column are all 1s.
(2) Each entry (i,j) for i,j ≥ 2 is the sum of all entries in the (i-1)×(j-1) sub-grid formed by rows 1..i-1 and columns 1..j-1.
We need to prove the value at the 8th row and 8th column is 2508.
-/
theorem combinatorics_609601 
    {x : ℕ → ℕ → ℕ} 
    (hx1 : ∀ j, x 1 j = 1) 
    (hx2 : ∀ i, x i 1 = 1)
    (hxi : ∀ i j, i ≥ 2 → j ≥ 2 → 
      x i j = ∑ k in range (i-1), ∑ l in range (j-1), x (k+1) (l+1)) :
    x 8 8 = 2508 := by
  
  simp [Finset.sum_range_succ, hx1, hx2, hxi]
