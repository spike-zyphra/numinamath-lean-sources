import Mathlib

open Finset

/-If four fair six-sided dice are rolled, what is the probability that the lowest number appearing on any die is exactly 3 ?-/

theorem combinatorics_609245:
  ((Icc 1 6 ×ˢ Icc 1 6 ×ˢ Icc 1 6 ×ˢ Icc 1 6).filter (fun (x, y, z, w) => min x (min y (min z w)) = 3)).card /
  (Icc 1 6 ×ˢ Icc 1 6 ×ˢ Icc 1 6 ×ˢ Icc 1 6).card = (175: ℚ) / 1296 := by

    native_decide