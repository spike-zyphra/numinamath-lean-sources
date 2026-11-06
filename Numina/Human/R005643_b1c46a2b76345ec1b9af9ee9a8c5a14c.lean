import Mathlib

open Finset

/-
Problem Analysis:
We need to count the number of ways to form a 5-person committee from 10 people, where the committee is formed by first electing 1 to 4 leaders, and then selecting the remaining members from the non-leaders.
-/
theorem combinatorics_609222 
    {N : ℕ} 
    (hN : N = 10) 
    (K : ℕ) 
    (hK : K = 5) :
    ∑ l in {1,2,3,4}, Nat.choose N l * Nat.choose (N - l) (K - l) = 7560 := by

  -- Substitute the values of N and K with 10 and 5 respectively
  subst hN hK

  -- Simplify binomial coefficients where applicable (e.g., C(n, 0) = 1, C(n, n) = 1)

  simp [Nat.choose_zero_right, Nat.choose_self]

  -- Use automated decision procedure to verify the equality
  decide