import Mathlib

open Finset

/-Let S=⌊M5⌋. Two integers m and n are chosen between 1 and S inclusive uniformly and independently at random.
What is the probability that m^n=n^m?-/

theorem number_theory_610013:
  ((Icc 1 12 ×ˢ Icc 1 12).filter (fun (x, y) => x ^ y = y ^ x)).card / (Icc 1 12 ×ˢ Icc 1 12).card = (7: ℚ) / 72 := by

    native_decide