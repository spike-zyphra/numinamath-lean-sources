import Mathlib
open Finset

/-The set $\{1,2, \ldots, 10\}$ is partitioned into three subsets $A, B$ and $C$. For each subset the sum of its elements, the product of its elements and the sum of the digits of all its elements are calculated. Is it possible that $A$ alone has the largest sum of elements, $B$ alone has the largest product of elements, and $C$ alone has the largest sum of digits?-/
theorem combinatorics_239551 :
    ∃ (A B C : Finset ℕ),
      A ∪ B ∪ C = Icc 1 10 ∧
      A ∩ B = ∅ ∧
      A ∩ C = ∅ ∧
      B ∩ C = ∅ ∧
      (∑ x ∈ A, x) > (∑ x ∈ B, x) ∧
      (∑ x ∈ A, x) > (∑ x ∈ C, x) ∧
      (∏ x ∈ B, x) > (∏ x ∈ A, x) ∧
      (∏ x ∈ B, x) > (∏ x ∈ C, x) ∧
      (∑ x ∈ C, (Nat.digits 10 x).sum) > (∑ x ∈ A, (Nat.digits 10 x).sum) ∧
      (∑ x ∈ C, (Nat.digits 10 x).sum) > (∑ x ∈ B, (Nat.digits 10 x).sum) := by
  -- Construct specific sets $A$, $B$, $C$.
  let A := ({1, 9, 10} : Finset ℕ)
  let B := ({2, 4, 5, 6} : Finset ℕ)
  let C := ({3, 7, 8} : Finset ℕ)
  use A, B, C
  -- Verify partition.
  have h_partition : A ∪ B ∪ C = Finset.Icc 1 10 ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ := by decide
  -- Verify sums.
  have h_sum : (∑ x ∈ A, x) = 20 ∧ (∑ x ∈ B, x) = 17 ∧ (∑ x ∈ C, x) = 18 := by tauto
  -- Verify products.
  have h_prod : (∏ x ∈ B, x) = 240 ∧ (∏ x ∈ A, x) = 90 ∧ (∏ x ∈ C, x) = 168 := by tauto
  -- Verify digit sums.
  have h_digit_sum : (∑ x ∈ C, (Nat.digits 10 x).sum) = 18 ∧
                      (∑ x ∈ A, (Nat.digits 10 x).sum) = 11 ∧
                      (∑ x ∈ B, (Nat.digits 10 x).sum) = 17 := by 
    constructor
    · rw [sum_insert, sum_insert, sum_singleton]
      have h₁: Nat.digits 10 3 = [3] := by norm_num
      have h₂: Nat.digits 10 7 = [7] := by norm_num
      have h₃: Nat.digits 10 8 = [8] := by norm_num
      rw [h₁, h₂, h₃]
      repeat norm_num
    · constructor
      · rw [sum_insert, sum_insert, sum_singleton]
        have h₁: Nat.digits 10 1 = [1] := by norm_num
        have h₂: Nat.digits 10 9 = [9] := by norm_num
        have h₃: Nat.digits 10 10 = [0, 1] := by norm_num
        rw [h₁, h₂, h₃]
        repeat norm_num
      · rw [sum_insert, sum_insert, sum_insert, sum_singleton]
        have h₁: Nat.digits 10 2 = [2] := by norm_num
        have h₂: Nat.digits 10 4 = [4] := by norm_num
        have h₃: Nat.digits 10 5 = [5] := by norm_num
        have h₄: Nat.digits 10 6 = [6] := by norm_num
        rw [h₁, h₂, h₃, h₄]
        repeat norm_num
  -- Combine conditions.
  have h_conditions : (∑ x ∈ A, x) > (∑ x ∈ B, x) ∧ (∑ x ∈ A, x) > (∑ x ∈ C, x) ∧
                      (∏ x ∈ B, x) > (∏ x ∈ A, x) ∧ (∏ x ∈ B, x) > (∏ x ∈ C, x) ∧
                      (∑ x ∈ C, (Nat.digits 10 x).sum) > (∑ x ∈ A, (Nat.digits 10 x).sum) ∧
                      (∑ x ∈ C, (Nat.digits 10 x).sum) > (∑ x ∈ B, (Nat.digits 10 x).sum) := by
    constructor
    · rw [h_sum.1, h_sum.2.1]; norm_num
    · constructor
      · rw [h_sum.1, h_sum.2.2]; norm_num
      · constructor
        · rw [h_prod.1, h_prod.2.1]; norm_num
        · constructor
          · rw [h_prod.1, h_prod.2.2]; norm_num
          · constructor
            · rw [h_digit_sum.1, h_digit_sum.2.1]; norm_num
            · rw [h_digit_sum.1, h_digit_sum.2.2]; norm_num
  exact ⟨h_partition.1, h_partition.2.1, h_partition.2.2.1, h_partition.2.2.2, h_conditions⟩
