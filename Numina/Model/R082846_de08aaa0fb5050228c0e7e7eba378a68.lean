import Mathlib

theorem number_theory_286530 : IsGreatest {p | p.Prime ∧ p ∣ ∑ i in (Finset.Ico 10 20).filter Nat.Prime, i} 5 := by
  have hsum : ∑ i in (Finset.Ico 10 20).filter Nat.Prime, i = 60 := by
    native_decide

  constructor

  · -- Show that 5 is in the set
    constructor
    · norm_num
    · rw [hsum]
      norm_num

  · -- Show that 5 is greatest in the set
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    rw [hsum] at h_div
    have h_le : p ≤ 60 := by
      exact Nat.le_of_dvd (by norm_num) h_div

    by_contra h
    push_neg at h

    interval_cases p <;> norm_num at h_prime h_div <;> norm_num [Nat.Prime] at h_prime <;> try { contradiction }