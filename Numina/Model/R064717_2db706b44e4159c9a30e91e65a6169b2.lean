import Mathlib

theorem number_theory_235280 : IsLeast {n | 1000 ∣ (n + 1) * (n + 2) * (n + 3) * (n + 4)} 121 := by
  constructor
  · -- Show that 121 is in the set
    norm_num
  · -- Show that 121 is the smallest
    intro n hn
    have h : 1000 ∣ (n + 1) * (n + 2) * (n + 3) * (n + 4) := hn
    by_contra h'
    push_neg at h'
    interval_cases n <;> norm_num at h ⊢ <;> omega