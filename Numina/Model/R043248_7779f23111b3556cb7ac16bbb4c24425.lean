import Mathlib
set_option maxRecDepth 1000000000000

theorem number_theory_130361 :
    IsLeast {p | p.Prime ∧ (p^3 + 2 * p^2 + p).divisors.card = 42} 23 := by
  constructor
  · -- Show 23 is in the set
    constructor
    · -- 23 is prime
      norm_num
    · -- Check that 23^3 + 2 * 23^2 + 23 has 42 divisors
      native_decide
  · -- Show 23 is the least
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime h_div
    <;> try { contradiction }