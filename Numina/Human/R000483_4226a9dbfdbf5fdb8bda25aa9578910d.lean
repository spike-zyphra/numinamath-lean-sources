import Mathlib
open Nat

/- In the prime factorization of $24!$, what is the exponent of $3$?  (Reminder: The number $n!$ is the product of the integers from 1 to $n$.  For example, $5!=5\cdot 4\cdot3\cdot2\cdot 1= 120$.) -/
theorem algebra_11221 : 24!.factorization 3 = 10 := by

  -- Change the type of the goal to `PartENat`.
  suffices h : (24!.factorization 3 : PartENat) = 10 by
    norm_cast at h

  -- Change Nat.factorization to multiplicity.
  rw [← multiplicity_eq_factorization Nat.prime_three (factorial_ne_zero 24)]

  -- We use Legendre's formula.
  -- 24 = (220) base 3
  -- The exponent of 3 in 24! is (24 - the sum of the digits of 24 in base 3) / (3 - 1) = 20 / 2 = 10.
  have H := Prime.sub_one_mul_multiplicity_factorial (n := 24) prime_three

  -- Simplify at H.
  -- And we get what we want.
  simp at H
  rw [show 20 = 2 * 10 by rfl,
      mul_left_cancel_iff_of_pos (by simp)] at H

  rw [H]
  norm_cast
