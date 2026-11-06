import Mathlib

theorem number_theory_161118 : IsLeast {n | ∃ k, n = k^2 ∧ (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset = {2, 0, 1, 6}} 2601 := by
  constructor
  · -- Show that 2601 is in the set
    use 51
    all_goals native_decide
  · -- Show that 2601 is the least in the set
    intro n hn
    rcases hn with ⟨k, rfl, hk1, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k < 51 := by
      nlinarith
    interval_cases k <;> norm_num at hk1 hk2 <;> norm_num at *
    all_goals try { contradiction }