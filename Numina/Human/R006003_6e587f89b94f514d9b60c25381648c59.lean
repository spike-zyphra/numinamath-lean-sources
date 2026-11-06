import Mathlib

open Finset

/-
Define P(n,m) as the number of paths from (0,0) to (n,m) on a grid
This is equivalent to the binomial coefficient C(n+m, n)
-/
def P (n m : ℕ) : ℕ := Nat.choose (n + m) n

/-
Theorem: Prove that the number of paths from (0,0) to (7,3) is 120
-/
theorem combinatorics_611031 
    {n m : ℕ} 
    (hn : n = 7) 
    (hm : m = 3) :
    P n m = 120 := by 

  -- Substitute n with 7 and m with 3 using the given equalities
  rw [hn, hm]
  decide