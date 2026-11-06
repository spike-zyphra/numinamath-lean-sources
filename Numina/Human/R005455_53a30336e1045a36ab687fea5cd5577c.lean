import Mathlib

open Finset

-- Define valid positions for row 2 (0-based index 1)
def row2_valid : Finset ℕ := 
  insert 0 (insert 1 (insert 3 (insert 4 (insert 6 (insert 7 (insert 9 ∅))))))

-- Define valid positions for row 4 (0-based index 3)
def row4_valid : Finset ℕ := 
  insert 0 (insert 3 (insert 6 (insert 7 (insert 9 ∅))))

-- Check if a given position (i, j) is valid in the grid
def is_valid (i j : ℕ) : Bool :=
  match i with
  | 0 => j ≤ 9  -- All positions in row 1 are valid
  | 1 => decide (j ∈ row2_valid) -- Row 2 has specific valid positions
  | 2 => j ≤ 9  -- All positions in row 3 are valid
  | 3 => decide (j ∈ row4_valid) -- Row 4 has specific valid positions
  | 4 => j ≤ 9  -- All positions in row 5 are valid
  | _ => false  -- Any other row is invalid

/-
Problem:
In the diagram below, how many distinct paths are there from January 1 to December 31, moving from one adjacent dot to the next either to the right, down, or diagonally down to the right?
-/
theorem Combinatorics_608374
    (a : ℕ → ℕ → ℕ) 
    (ha_rec : ∀ i j, is_valid i j → 
    a i j = 
      (if j > 0 ∧ is_valid i (j-1) then a i (j-1) else 0) +  
      (if i > 0 ∧ is_valid (i-1) j then a (i-1) j else 0) +
      (if i > 0 ∧ j > 0 ∧ is_valid (i-1) (j-1) then a (i-1) (j-1) else 0))  
    (ha_start : a 0 0 = 1) :
    a 4 9 = 372 := by

  -- Base case: starting position (0,0) has exactly 1 path
  have h0 : is_valid 0 0 := by simp [is_valid]

  have h1 := ha_rec 0 0 h0 

  norm_num [is_valid, row2_valid, row4_valid] at h1 

  -- Use omega tactic to automatically solve arithmetic goals in the proof
  all_goals 
  
    omega  