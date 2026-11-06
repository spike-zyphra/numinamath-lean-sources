import Mathlib

open Finset

/-
Theorem: Calculate the number of valid paths for an ant moving from (0,0) to (5,5) with the constraint that it cannot move in the same direction more than twice consecutively.
-/
theorem combinatorics_608752 
    {f : ℕ → ℕ} 
    (hf1 : f 3 = 3) 
    (hf2 : f 4 = 4) 
    (hf3 : f 5 = 1) 
    (hf : ∀ n, n ≤ 5 → f n = {a : ℕ → ℕ | (∀ i, a i = 1 ∨ a i = 2) ∧ (∑ i ∈ Icc 1 n, a i) = 5}.ncard) : 
    2 * (f 3 ^ 2 + f 3 * f 4 + f 4 ^ 2 + f 4 * f 5 + f 5 ^ 2) = 84 := by 

  -- Compute f(3), f(4), and f(5) using the given constraints
  have h₁ := hf 3 (by norm_num)
  have h₂ := hf 4 (by norm_num)
  have h₃ := hf 5 (by norm_num)
  
  -- Substitute the known values of f(3), f(4), and f(5) to verify the total count
  norm_num [hf1, hf2, hf3, Set.ncard_eq_zero] at h₁ h₂ h₃ ⊢