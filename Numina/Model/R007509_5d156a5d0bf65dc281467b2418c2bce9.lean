import Mathlib

theorem number_theory_18982 :
    IsLeast {n | 0 < n ∧ 80325 ∣ Nat.factorial n} 17 := by
  constructor
  · -- Show that 17 is in the set
    constructor
    · norm_num
    · -- Show that 80325 divides 17!
      native_decide
  · -- Show that 17 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> simp [Nat.factorial] at hn_div <;> all_goals omega