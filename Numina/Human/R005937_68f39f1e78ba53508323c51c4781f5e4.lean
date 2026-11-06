import Mathlib

open Nat Finset

/-A grid is called groovy if each cell of the grid is labeled with the smallest positive integer that does not appear below it in the same column or to the left of it in the same row. Compute the sum of the entries of a groovy $14 \times 14$ grid whose bottom left entry is 1 .
-/

-- Helper function to count numbers in range [0, 14-1] where bit `b` is 0 or 1.
-- `is_one = true` counts numbers where bit `b` is 1 (N₁(b)).
-- `is_one = false` counts numbers where bit `b` is 0 (N₀(b)).
def count_numbers_with_bit_val (b : ℕ) (is_one : Bool) : ℕ :=
  (Finset.range 14).filter (fun x => Nat.testBit x b = is_one) |>.card

-- Lemmas for N₀(b) and N₁(b) for b = 0, 1, 2, 3, for numbers in range [0, 13]
lemma N0_bit0 : count_numbers_with_bit_val 0 false = 7 := by
  unfold count_numbers_with_bit_val 
  -- Counts even numbers in [0,13]: 0,2,4,6,8,10,12
  rfl 

lemma N1_bit0 : count_numbers_with_bit_val 0 true = 7 := by
  unfold count_numbers_with_bit_val 
  -- Counts odd numbers in [0,13]: 1,3,5,7,9,11,13
  rfl

lemma N0_bit1 : count_numbers_with_bit_val 1 false = 8 := by
  unfold count_numbers_with_bit_val 
  -- Counts numbers in [0,13] where 2nd bit is 0 (x mod 4 in {0,1}): 0,1,4,5,8,9,12,13
  rfl

lemma N1_bit1 : count_numbers_with_bit_val 1 true = 6 := by
  unfold count_numbers_with_bit_val 
  -- Counts numbers in [0,13] where 2nd bit is 1 (x mod 4 in {2,3}): 2,3,6,7,10,11
  rfl

lemma N0_bit2 : count_numbers_with_bit_val 2 false = 8 := by
  unfold count_numbers_with_bit_val 
  -- Counts numbers in [0,13] where 3rd bit is 0 (x mod 8 in {0,1,2,3}): 0,1,2,3,8,9,10,11
  rfl

lemma N1_bit2 : count_numbers_with_bit_val 2 true = 6 := by
  unfold count_numbers_with_bit_val 
  -- Counts numbers in [0,13] where 3rd bit is 1 (x mod 8 in {4,5,6,7}): 4,5,6,7,12,13
  rfl

lemma N0_bit3 : count_numbers_with_bit_val 3 false = 8 := by
  unfold count_numbers_with_bit_val 
  -- Counts numbers in [0,13] where 4th bit is 0 (x mod 16 in {0..7}): 0,1,2,3,4,5,6,7
  rfl

lemma N1_bit3 : count_numbers_with_bit_val 3 true = 6 := by
  unfold count_numbers_with_bit_val 
  -- Counts numbers in [0,13] where 4th bit is 1 (x mod 16 in {8..15}): 8,9,10,11,12,13
  rfl

-- Calculate S_XOR = ∑_{i=0}^{N-1} ∑_{j=0}^{N-1} (i XOR j)
-- This is equivalent to ∑_{bit_idx} 2^bit_idx * (2 * N₀(bit_idx) * N₁(bit_idx))
def S_XOR_val : ℕ :=
  (2^0 * (2 * (count_numbers_with_bit_val 0 false) * (count_numbers_with_bit_val 0 true))) +
  (2^1 * (2 * (count_numbers_with_bit_val 1 false) * (count_numbers_with_bit_val 1 true))) +
  (2^2 * (2 * (count_numbers_with_bit_val 2 false) * (count_numbers_with_bit_val 2 true))) +
  (2^3 * (2 * (count_numbers_with_bit_val 3 false) * (count_numbers_with_bit_val 3 true)))

lemma S_XOR_val_eq_1442 : S_XOR_val = 1442 := by
  unfold S_XOR_val
  rw [N0_bit0, N1_bit0, N0_bit1, N1_bit1, N0_bit2, N1_bit2, N0_bit3, N1_bit3]
  norm_num

-- The value in cell (i,j) is (i XOR j) + 1.
-- The sum is S_XOR + 14^2
def total_sum_groovy_grid : ℕ := S_XOR_val + 14^2

theorem combinatorics_610815 : total_sum_groovy_grid = 1638 := by
  unfold total_sum_groovy_grid 
  rw [S_XOR_val_eq_1442]
  norm_num -- Computes 1442 + 14^2 = 1442 + 196 = 1638
