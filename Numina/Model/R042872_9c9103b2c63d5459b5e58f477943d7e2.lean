import Mathlib


/-
Two fair octahedral dice, each with the numbers 1 through 8 on their faces, are rolled.
Let $N$ be the remainder when the product of the numbers showing on the two dice is divided by 8 . Find the expected value of $N$.
-/


-- Define the type for the outcome of a single die roll.  Using `Fin 8` directly.
abbrev DieResult := Fin 8

-- Define the type for the outcome of rolling two dice.
abbrev TwoDiceResult := DieResult × DieResult

-- Define the function to calculate N (remainder when the product is divided by 8).
def N (ω : TwoDiceResult) : Nat := (ω.1.val.succ * ω.2.val.succ) % 8

-- Calculate the expected value of N.  This is the core computation.
def expected_N : ℚ :=
  (∑ (ω : TwoDiceResult), (N ω : ℚ) / 64)  -- Sum over all outcomes, divide by total outcomes

theorem numbertheory_609251 : expected_N = 11 / 4 := by
  unfold expected_N
  native_decide