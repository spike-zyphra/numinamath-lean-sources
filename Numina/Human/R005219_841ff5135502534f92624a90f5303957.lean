import Mathlib

open Finset

/-
A graph has $N$ vertices. An invisible hare sits in one of the vertices. A group of hunters tries to kill the hare. In each move all of them shoot simultaneously: each hunter shoots at a single vertex, they choose the target vertices cooperatively. If the hare was in one of the target vertices during a shoot, the hunt is finished. Otherwise the hare can stay in its vertex or jump to one of the neighboring vertices.
-/
theorem combinatorics_606324 
    {N : ℕ} 
    (hN : 0 < N) 
    (a : ℕ → ℕ)
    (ha : a 0 = N) 
    (h : ∀ i, a (i + 1) ≤ a i + N) :
    ∃ b : ℕ → ℕ, b 0 = N ∧ (∀ i, b (i + 1) ≤ b i + 2 ^ N) := by

  -- Define the optimal strategy's smell set size as constant N (simplest case)
  use fun i => N
  constructor

  · -- Initial condition: the smell set starts as the entire graph (size N)
    simp [ha]
  intro i

  -- Prove that the next smell set size is bounded by current size plus 2^N
  have h₁ : N ≤ N + 2 ^ N := by

    -- Establish that 2^N is positive (since N > 0)
    have h₂ : 0 < 2 ^ N := by
      exact pow_pos (by norm_num) N

    -- Use arithmetic to show N ≤ N + 2^N
    have h₃ : N ≤ N + 2 ^ N := by
      omega
    exact h₃

  -- Reuse the established bound
  have h₄ : N ≤ N + 2 ^ N := h₁
  
  -- Trivially show N is non-negative (useful for arithmetic reasoning)
  have h₅ : 0 ≤ N := by
    linarith

  -- Reaffirm the bound using linear arithmetic
  have h₆ : N ≤ N + 2 ^ N := by
    linarith

  -- Restate the original growth condition for clarity
  have h₇ : ∀ i, a (i + 1) ≤ a i + N := by
    intro i
    exact h i

  -- Recall the initial condition
  have h₈ : a 0 = N := ha
  
  -- Use automated reasoning to conclude the proof
  omega