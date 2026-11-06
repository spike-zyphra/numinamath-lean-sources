import Mathlib

theorem number_theory_3901 : IsGreatest {p : ℕ | p.Prime ∧ p ∣ (6 * 14 * 22)} 11 := by
  constructor
  · -- Show 11 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show there is no greater element in the set
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    by_contra h
    push_neg at h
    have h1 : p ≤ 6 * 14 * 22 := by
      exact Nat.le_of_dvd (by norm_num) hdiv
    have h2 : p < 1849 := by
      linarith
    interval_cases p <;> norm_num at h_prime hdiv <;> try { contradiction }