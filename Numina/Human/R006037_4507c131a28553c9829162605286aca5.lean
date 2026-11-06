import Mathlib

open Finset

/-
Problem:
A knight starts on a white square of a chessboard. Each move alternates between white and black squares. Landing on a black square earns 2 carrots. Each move (regardless of landing on white or black) costs 1 carrot. The knight must return to the starting square, which is white.
-/
theorem combinatorics_611226 : 
    IsGreatest {n : ℕ | ∃ w b : ℕ, 
    w + b > 0 ∧ w = b + 1 ∧ n = 2 * b - (b + w) } 0 := by

  -- Prove that 0 is an element of the set and is the upper bound
  constructor
  · 
    -- Provide witness values w=1, b=0 to show the set is non-empty
    use 1, 0

    -- Use omega tactic to automatically verify arithmetic constraints
    all_goals omega
  · 
    -- Prove that any element n in the set must be ≤ 0
    intro n hn

    -- Extract w and b from the existential statement
    rcases hn with ⟨w, b, hwbp, hw, hn⟩

    -- Rewrite the equation using w = b + 1
    rw [hw] at hn  

    -- Use omega to show that n must be 0 given the constraints
    have hn' : n = 0 := by omega 
    
    -- Conclude that n ≤ 0 using the equality
    exact le_of_eq hn'


