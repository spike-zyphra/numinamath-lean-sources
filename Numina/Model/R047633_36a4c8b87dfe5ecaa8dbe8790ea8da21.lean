import Mathlib

theorem number_theory_256292 : IsGreatest {p | p.Prime ∧ p ∣ 2006} 59 := by
  constructor
  · -- Show 59 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show there is no larger element in the set
    intro p hp
    rcases hp with ⟨h_prime, hdiv⟩
    have h5 : p ∣ 2006 := hdiv
    have h6 : p ∣ 2 ∨ p ∣ 17 ∨ p ∣ 59 := by
      have h7 : p ∣ 2 * 17 * 59 := by
        norm_num at *
        all_goals try tauto
      have h8 : p ∣ 2 ∨ p ∣ (17 * 59) := by
        apply (Nat.Prime.dvd_mul h_prime).1
        all_goals try norm_num
        all_goals try assumption
        all_goals try tauto
      rcases h8 with (h8 | h8)
      · tauto
      · -- p divides 17 * 59
        have h9 : p ∣ 17 ∨ p ∣ 59 := by
          apply (Nat.Prime.dvd_mul h_prime).1
          all_goals try norm_num
          all_goals try assumption
        tauto
    by_contra h
    push_neg at h
    rcases h6 with (h | h | h)
    · -- Assume p divides 2
      have h8 : p ≤ 2 := by
        exact Nat.le_of_dvd (by norm_num) h
      nlinarith
    · -- Assume p divides 17
      have h8 : p ≤ 17 := by
        exact Nat.le_of_dvd (by norm_num) h
      nlinarith
    · -- Assume p divides 59
      have h8 : p ≤ 59 := by
        exact Nat.le_of_dvd (by norm_num) h
      nlinarith