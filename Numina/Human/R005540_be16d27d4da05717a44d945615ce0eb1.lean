import Mathlib

open Finset Real Nat

/-
Theorem: Probability of getting more heads than tails in 5 coin flips
-/
theorem combinatorics_608738 : 
    ((3 : ℕ) ∈ Icc 1 5 → 
    (∑ n ∈ Icc 3 5, Nat.choose 5 n * (2 / 3) ^ n * (1 / 3) ^ (5 - n) : ℝ) = (64 / 81 : ℝ)) := by

  intro h

  norm_num 

  simp_all [Finset.sum_Icc_succ_top]

  ring_nf

  have t₁ : Nat.choose 5 3 = 10 := by rfl

  rw [t₁] at *
  
  norm_num

  

