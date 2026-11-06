import Mathlib

theorem number_theory_4631_a (ndimes nquar : ℕ)
  -- a quarter is worth 25 cents and a dime is worth 10 cents.
  -- So we can represent the total amount in cent as : $ndimes * 10 + nquar * 25 = 100$.
  (h : ndimes * 10 + nquar * 25 = 100) :
  ndimes = 10 ∧ nquar = 0 ∨ ndimes = 5 ∧ nquar = 2 ∨ ndimes = 0 ∧ nquar = 4 := by
  omega