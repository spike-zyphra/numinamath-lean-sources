import Mathlib

/- The expression 2021 / 2020 − 2020 / 2021​ is equal to the fraction p / q​ in which p and q are positive integers 
whose greatest common divisor is 1. What is p?
(A) 1 (B) 9 (C) 2020 (D) 2021 (E) 4041 -/
theorem algebra_93465 : ∃ q : ℕ, Nat.gcd 4041 q = 1 ∧ ((2021 / 2020 - 2020 / 2021) : ℚ) = 4041 / q := by {
  -- Specify the right denominator
  use 2020*2021
  -- Split into two goals
  constructor
  -- Verify coprimality
  norm_num
  -- Verify the equality of fractions
  norm_num
}