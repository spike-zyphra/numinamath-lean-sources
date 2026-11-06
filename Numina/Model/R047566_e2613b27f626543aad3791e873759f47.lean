import Mathlib

theorem number_theory_609606: ∑ d ∈ Nat.divisors 2016, ((1 / (Nat.divisors 2016).card) * ((d^2: ℚ) / (d^2 + 2016))) = 1 / 2 := by
  native_decide