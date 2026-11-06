import Mathlib

open Finset

abbrev isGood (n : ℕ) := (Nat.digits 10 n).count 2 > (Nat.digits 10 n).count 3

abbrev isBad (n : ℕ) := (Nat.digits 10 n).count 3 > (Nat.digits 10 n).count 2

theorem number_theory_35935 : ((Icc 1 2023).filter isGood).card - ((Icc 1 2023).filter isBad).card = (22 : ℤ) := by
  native_decide