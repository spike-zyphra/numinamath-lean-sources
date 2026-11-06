import Mathlib

open Nat

/- The product of all the prime numbers between 1 and 100 is equal to $P$. What is the remainder when $P$ is divided by 16? -/
theorem number_theory_19466 : (∏ p in (Nat.primesBelow 100), p) % 16 = 6 := by
  exact rfl