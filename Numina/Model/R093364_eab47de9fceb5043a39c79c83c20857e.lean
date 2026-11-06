import Mathlib

theorem number_theory_4521 : IsGreatest {p | p.Prime ∧ p ∣ (6 * 14 * 22)} 11 := by 
  constructor
  · -- Show that 11 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that any element in the set is ≤ 11
    intro p hp
    rcases hp with ⟨h1, h2⟩
    have h4 : p ∣ 1848 := by
      norm_num at h2 ⊢
      exact_mod_cast h2
    have h5 : p ≤ 1848 := by
      exact_mod_cast (Nat.le_of_dvd (show 0 < 1848 by norm_num) h4)
    by_contra h6
    push_neg at h6
    interval_cases p <;> norm_num at h1 h4 <;> tauto