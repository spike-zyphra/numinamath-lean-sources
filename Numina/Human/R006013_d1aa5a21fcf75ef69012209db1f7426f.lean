import Mathlib

open Finset Real

/-
Theorem: Probability that all switches end up ON after the operation is 1/2^2002
-/
theorem combinatorics_611104 
    (n n₁ n₂ : ℕ)
    (hn : n = n₁ + n₂) 
    (N₁ : n₁ = ∑ x ∈ range 2003, if x % 2 = 0 then 1 else 0)
    (N₂ : n₂ = ∑ x ∈ range 2003, if x % 2 = 0 then 0 else 1) :
    2 / 2 ^ n = (1 / 2 ^ 2002 : ℝ) := by 

  field_simp [Nat.pow_succ]
  
  have t₁ : 2 * 2 ^ 2002= 2^2003 := by linarith
  
  -- Calculate the number of even numbers in the range 0..2002. Since 2003 is odd, there are (2003 + 1) / 2 = 1002 even numbers
  have t₂ : (∑ x ∈ range 2003, if x % 2 = 0 then 1 else 0) = 1002 := by native_decide
  
  -- Calculate the number of odd numbers in the range 0..2002. Since 2003 is odd, there are (2003 - 1) / 2 = 1001 odd numbers
  have t₃ : (∑ x ∈ range 2003, if x % 2 = 0 then 0 else 1) = 1001 := by native_decide
  
  have t₄ : n = 2003 := by linarith
  rw [t₄] at *
  ring_nf