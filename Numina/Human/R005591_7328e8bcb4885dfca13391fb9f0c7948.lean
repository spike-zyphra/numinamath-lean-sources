import Mathlib

open Finset Real 

/-
Problem:
This problem arises in combinatorial mathematics, specifically in the study of permutation statistics. Given a permutation π of {1, 2, ..., n}, define f(π) as the smallest positive integer i such that the subarray π(1), π(2), ..., π(i) is a permutation of {1, 2, ..., i}. The goal is to compute. the sum of f(π) over all permutations π of {1, 2, ..., 7}.
-/
theorem combinatorics_609019 
    {g : ℕ → ℕ}
    (g₀ : g 1 = 1)
    (hgn : ∀ n > 1 ,
    g n = n.factorial - ∑ k in Icc 1 (n-1) , g k * (n - k).factorial) : 
    ∑ k ∈ Icc 1 7, k * g k * (7 - k).factorial = 29093 := by

  -- Extract recursive relations for n=2 to n=7 using the given hgn
  have h₁ := hgn 2 (by decide)  -- Recursion for g(2)
  have h₂ := hgn 3 (by decide)  -- Recursion for g(3)
  have h₃ := hgn 4 (by decide)  -- Recursion for g(4)
  have h₄ := hgn 5 (by decide)  -- Recursion for g(5)
  have h₅ := hgn 6 (by decide)  -- Recursion for g(6)
  have h₆ := hgn 7 (by decide)  -- Recursion for g(7)

  -- Simplify the recursive relations using numerical normalization
  norm_num [Icc_self, Finset.sum_singleton, Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_mul] at h₁ h₂ h₃ h₄ h₅ h₆

  -- Calculate specific values of g(n) for n=2 to n=7
  -- g(2) = 1
  have g₁ : g 2 = 1 := by omega 

  -- g(3) = 3
  have g₂ : g 3 = 3 := by        
    have g₂₁ : 6 - ∑ x ∈ Icc 1 2 , g x * (3 - x).factorial = 6 - (g 1 * (3 - 1).factorial + g 2 * (3 - 2).factorial) := by exact rfl
    have g₂₂: 6 - (g 1 * (3 - 1).factorial + g 2 * (3 - 2).factorial) = 3 := by
      rw [g₀ , g₁] 
      simp
    omega

  -- g(4) = 13
  have g₃ : g 4 = 13 := by
    have g₃₁ : 24 - ∑ x ∈ Icc 1 3 , g x * (4 - x).factorial = 24 - (g 1 * (4 - 1).factorial + g 2 * (4 - 2).factorial + g 3 * (4 - 3).factorial) := by 
      simp [Finset.sum_Icc_succ_top, Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
    have g₃₂ : 24 - (g 1 * (4 - 1).factorial + g 2 * (4 - 2).factorial + g 3 * (4 - 3).factorial) = 13 := by
      rw [g₀ , g₁ , g₂] 
      exact rfl
    omega

  -- g(5) = 71
  have g₄ : g 5 = 71 := by       
    have g₄₁ : 120 - ∑ x ∈ Icc 1 4 , g x * (5 - x).factorial = 120 - (g 1 * (5 - 1).factorial + g 2 * (5 - 2).factorial + g 3 * (5 - 3).factorial + g 4 * (5 - 4).factorial) := by 
      simp [Finset.sum_Icc_succ_top, Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
    have g₄₂: 120 - (g 1 * (5 - 1).factorial + g 2 * (5 - 2).factorial + g 3 * (5 - 3).factorial + g 4 * (5 - 4).factorial) = 71 := by
      rw [g₀ , g₁ , g₂ , g₃] 
      simp 
      exact rfl
    omega

  -- g(6) = 461
  have g₅ : g 6 = 461 := by
    have g₅₁ : 720 - ∑ x ∈ Icc 1 5 , g x * (6 - x).factorial = 720 - (g 1 * (6 - 1).factorial + g 2 * (6 - 2).factorial + g 3 * (6 - 3).factorial + g 4 * (6 - 4).factorial + g 5 * (6 - 5).factorial) := by 
      simp [Finset.sum_Icc_succ_top, Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
    have g₅₂ : 720 - (g 1 * (6 - 1).factorial + g 2 * (6 - 2).factorial + g 3 * (6 - 3).factorial + g 4 * (6 - 4).factorial + g 5 * (6 - 5).factorial) = 461 := by
      rw [g₀ , g₁ , g₂ , g₃ , g₄] 
      simp 
      exact rfl
    omega

  -- g(7) = 3447
  have g₆ : g 7 = 3447 := by
    have g₆₁ : 5040 - ∑ x ∈ Icc 1 6 , g x * (7 - x).factorial = 5040 - (g 1 * (7 - 1).factorial + g 2 * (7 - 2).factorial + g 3 * (7 - 3).factorial + g 4 * (7 - 4).factorial + g 5 * (7 - 5).factorial + g 6 * (7 - 6).factorial) := by 
      simp [Finset.sum_Icc_succ_top, Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
    have g₆₂ : 5040 - (g 1 * (7 - 1).factorial + g 2 * (7 - 2).factorial + g 3 * (7 - 3).factorial + g 4 * (7 - 4).factorial + g 5 * (7 - 5).factorial + g 6 * (7 - 6).factorial) = 3447 := by
      rw [g₀ , g₁ , g₂ , g₃ , g₄ , g₅] 
      simp 
      exact rfl
    omega

  -- Expand the total sum into individual terms from k=1 to k=7
  have H : ∑ k ∈ Icc 1 7 , k * g k * (7 - k).factorial = 1 * g 1 * (6).factorial + 2 * g 2 * (5).factorial + 3 * g 3 * (4).factorial + 4 * g 4 * (3).factorial + 5 * g 5 * (2).factorial + 6 * g 6 * (1).factorial+7 * g 7 * (0).factorial := by 
      simp [Finset.sum_Icc_succ_top, Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]

  -- Substitute the computed values of g(n) into the expanded sum and verify it equals 29093
  rw [H , g₁ , g₂ , g₃ , g₄ , g₅ , g₆ , g₀]
  decide
  