import Mathlib

open Finset 

/-What is the probability that two cards randomly selected (without replacement) from a standard 52 -card deck
are neither of the same value nor the same suit?-/

theorem combinatorics_611454: ((Finset.range 52 ×ˢ Finset.range 52).filter (fun (x, y) => x / 13 ≠ y / 13 ∧ x % 13 ≠ y % 13)).card /
  ((Finset.range 52 ×ˢ Finset.range 52).filter (fun (x, y) => x ≠ y)).card = (12: ℚ) / 17 := by

  -- here we number the cards by: 0-12: suit 1; 13-25: suit 2; ..., 38-51: suit 4, each suit has 13 cards
  -- then the number of all possible pairs allowed is
  -- ((Finset.range 52 ×ˢ Finset.range 52).filter (fun (x, y) => x / 13 ≠ y / 13 ∧ x % 13 ≠ y % 13)).card

  native_decide