import Mathlib

/- the sum of properDivisors -/
abbrev sigma (n : ℕ) := ∑ d ∈ n.properDivisors, d

/- def amicable pair -/
abbrev is_amicable_pair (n m : ℕ) := (sigma n = m ∧ sigma m = n)

theorem number_theory_4920 : (is_amicable_pair 220 284) ∧ (is_amicable_pair 1184 1210) ∧ (is_amicable_pair 79750 88730) := by
  unfold is_amicable_pair sigma
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide