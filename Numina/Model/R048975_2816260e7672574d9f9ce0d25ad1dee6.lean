import Mathlib

theorem number_theory_288728 : IsLeast {p | p.Prime ∧ p ∣ (10^2011 + 1)} 11 := by
  constructor
  · -- Show that 11 is in the set {p | p.Prime ∧ p ∣ (10^2011 + 1)}
    constructor
    · -- Show 11 is prime
      norm_num
    · -- Show 11 divides 10^2011 + 1
      native_decide
  · -- Show that 11 is the least prime divisor
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at *
    <;> contradiction