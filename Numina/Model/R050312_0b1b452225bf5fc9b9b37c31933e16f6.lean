import Mathlib

theorem number_theory_240792 {Q : ℕ} (hQ : Q = (Nat.digits 10 ((2^222)^5 * (5^555)^2)).length) :
    IsGreatest {p | p.Prime ∧ p ∣ Q} 101 := by
  have h1 : Q = 1111 := by
    rw [hQ]
    native_decide
  rw [h1]
  constructor
  · -- Show that 101 is in the set
    constructor
    · -- Show that 101 is prime
      norm_num
    · -- Show that 101 divides 1111
      norm_num
  · -- Show that any element in the set is ≤ 101
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    have : p ≤ 1111 := by
      exact Nat.le_of_dvd (by norm_num) h_div
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h_div <;> all_goals tauto