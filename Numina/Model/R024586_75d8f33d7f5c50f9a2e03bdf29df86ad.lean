import Mathlib

theorem number_theory_16228 : IsGreatest {p | p.Prime ∧ p ∣ (3^7 + 6^6)} 67 := by
  constructor
  · -- First show 67 is in the set, so it is prime and divides 3^7 + 6^6
    constructor
    · norm_num
    · norm_num
  · -- Show that for any p in the set, p ≤ 67
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    have h4 : p ∣ 3^6 * 67 := by
      norm_num at h_div ⊢
      exact h_div
    have h5 : p ∣ 3^6 ∨ p ∣ 67 := by
      apply (Nat.Prime.dvd_mul h_prime).mp
      all_goals try { tauto }
    rcases h5 with h6 | h7
    · -- Assume h6: p divides 3^6
      have h8 : p ∣ 3 := by
        have h8 : p ∣ 3 ^ 6 := by
          simpa using h6
        have h9 : p ∣ 3 := by
          exact Nat.Prime.dvd_of_dvd_pow h_prime h8
        exact h9
      have h10 : p ≤ 3 := by
        exact Nat.le_of_dvd (by norm_num) h8
      omega
    · -- Assume h7: p divides 67
      have h8 : p ∣ 67 := h7
      have h9 : p ≤ 67 := by
        exact Nat.le_of_dvd (by norm_num) h8
      omega