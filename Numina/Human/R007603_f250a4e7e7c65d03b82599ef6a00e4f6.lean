import Mathlib
/-
If no one shares an office, in how many ways can 3 people be assigned to 5 different offices? (Each person gets exactly one office).-/
open Nat

theorem algebra_3951 {n m : ℕ} (hn : n = 3) (hm : m = 5) :

    n ! * m.choose n = 60 := by
    have gez :  0 < n  := by linarith
    have eq :  n * (n - 1) !  =   n !  := by
      apply mul_factorial_pred gez
    --If we number the three people 1, 2, and 3, there are $5$ offices that person 1 can be assigned to, $4$ offices that person 2 can be assigned to, and $3$ offices that person 3 can be assigned to. This gives us $5 \times 4 \times 3 = \boxed{60}$ ways to assign the three people to offices.
    rw [←  eq]
    rw [hm]; rw [hn] ; rw [choose];rw [choose]
    simp