import Mathlib

/- How many six-digit multiples of 27 have only 3,6 , or 9 as their digits? -/
theorem number_theory_610205 : {n ∈ Finset.Ico (10 ^ 5) (10 ^ 6) | 27 ∣ n ∧ Nat.digits 10 n ⊆ {3, 6, 9}}.card = 51 := by
  -- The goal is to count the number of six-digit multiples of 27 that have only 3,6, or 9 as their digits.
  -- The numbers are stated as a Finset, so we can use the `card` function to count them.
  -- And the goal is computably verifiable.
  -- So we use `native_decide` to finish the proof.
  native_decide
