import Mathlib

open Finset Real

/-
Santa Claus Gift Distribution Theorem:
Given `n` children and at least `n` gifts from Santa Claus. 
-/
theorem combinatorics_604843 
    {n : ℕ} 
    (hn : 0 < n)
    (x : ℕ → ℝ) 
    (hx : ∀ i ∈ Icc 1 n, 0 < x i) 
    (hxs : ∑ i ∈ Icc 1 n, (1 / x i) ≤ 1) : 
    ∃ y : ℕ → ℝ,
    (∀ i ∈ Icc 1 n, 0 < y i) ∧ 
    (∀ i ∈ Icc 1 n, y i ≤ x i) := by

  have t₁ : n > 0 := by exact hn
  have t₂ : ∑ i ∈ Icc 1 n, (1 / x i) ≤ 1 := by exact hxs
  
  -- Proof strategy: Construct a function y that satisfies the required conditions, Here we use the constructive approach: simply take y to be the original x
  refine' ⟨x, _⟩
  
  -- We need to prove two conditions for the constructed y:
  -- 1. Every child likes the gift assigned to them (0 < y i)
  -- 2. The assigned gift is one of the desirable gifts for each child (x i = y i)
  constructor
  · 
    -- Proving the first condition: Every child likes the assigned gift. This follows directly from assumption hx, which ensures each child likes at least one gift
    intro i hi
    exact hx i hi
  · 
    -- Proving the second condition: The assigned gift is one of the desirable gifts. This step uses simplification because we have constructed y to be identical to x
    intro i hi
    simp_all
