import Mathlib

open Finset

/-
This theorem solves the problem of counting the number of ways to color a 6×6 grid such that
each row and each column contains exactly two red squares. The solution involves combinatorial
analysis and dynamic programming to derive the result.
-/
theorem combinatorics_608976 
    {f : ℕ → ℕ}
    (hf0 : f 0 = 1)
    (hfn : ∀ n , f (n) = ∑ k in Icc 2 n, 1 / 2 * (f (n - k)) * n.factorial * (n - 1).factorial / ((n - k).factorial * (n - k).factorial)) :
    f 6 = 67950 := by

  -- Compute the recurrence relation for n = 0 to 6
  have h₁ := hfn 0
  have h₂ := hfn 1
  have h₃ := hfn 2
  have h₄ := hfn 3
  have h₅ := hfn 4
  have h₆ := hfn 5
  have h₇ := hfn 6
  
  -- Normalize numerical expressions using the recurrence relation and factorial properties
  norm_num [hf0, Nat.factorial_succ, Nat.div_eq_of_lt, Nat.mul_div_assoc, Nat.mul_assoc] at h₁ h₂ h₃ h₄ h₅ h₆ h₇