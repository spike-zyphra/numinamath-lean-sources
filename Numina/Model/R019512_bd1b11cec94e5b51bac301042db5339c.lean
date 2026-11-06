import Mathlib

theorem number_theory_39505 : IsGreatest {p | p.Prime ∧ 2020 % p = 6} 53 := by
  constructor
  · -- Show 53 is in the set
    constructor
    · -- Show 53 is prime
      norm_num
    · -- Show 2020 % 53 = 6
      norm_num
  · -- Show that 53 is greatest in the set
    intro p hp
    rcases hp with ⟨h_prime, h_mod⟩
    by_contra h
    push_neg at h
    have h5 : p ≤ 2020 := by
      by_contra h1
      push_neg at h1
      have h6a : p > 2020 := by linarith
      have h6b : 2020 % p = 2020 := by
        rw [Nat.mod_eq_of_lt]
        all_goals omega
      linarith
    interval_cases p <;> norm_num at h_prime h_mod <;> tauto