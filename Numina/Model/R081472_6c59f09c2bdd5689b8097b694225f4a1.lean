import Mathlib

theorem number_theory_6929 :
    IsLeast {n : ℕ | Odd n ∧ (Nat.digits 10 n).length ≥ 3 ∧ (Nat.digits 10 n).toFinset.card ≥ 3} 103 := by
  constructor
  · -- Show 103 is in the set
    refine ⟨by decide, ?_, ?_⟩
    · -- Show that 103 has >= 3 digits in base 10
      native_decide
    · -- Show that digits of 103 have >= 3 unique digits
      native_decide
  · -- Show that 103 is the smallest such number
    intro n hn
    rcases hn with ⟨h_odd, h_digits, h_card⟩
    by_contra h
    push_neg at h
    have h1 : n < 103 := by linarith
    have h2 : n >= 100 := by
      by_contra h'
      push_neg at h'
      interval_cases n <;> norm_num at h_digits <;> all_goals 
        try { contradiction }
        <;> norm_num at h_card <;> all_goals 
          try { contradiction }
    interval_cases n <;> norm_num at h_odd h_digits h_card <;> all_goals 
      try { contradiction }