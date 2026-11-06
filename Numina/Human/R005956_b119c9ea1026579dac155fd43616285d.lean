import Mathlib

open Finset

/-Alice, Bob, and Charlie each pick a 2-digit number at random. What is the probability that all of their numbers' tens' digits are different from each others' tens' digits and all of their numbers' ones digits are different from each others' ones' digits?-/

theorem combinatorics_610912: ((Icc 10 99 ×ˢ Icc 10 99 ×ˢ Icc 10 99).filter (fun (x, y, z) =>
  x / 10 ≠ y / 10 ∧ y / 10 ≠ z / 10 ∧ z / 10 ≠ x / 10 ∧ x % 10 ≠ y % 10 ∧ y % 10 ≠ z % 10 ∧ z % 10 ≠ x % 10)).card / 
  (Icc 10 99 ×ˢ Icc 10 99 ×ˢ Icc 10 99).card 
    = (112: ℚ) / 225 := by
    
      native_decide