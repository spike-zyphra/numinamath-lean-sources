import Mathlib

theorem number_theory_53999 :
    IsLeast {m : ℕ | 0 < m ∧ Nat.lcm 15 m = Nat.lcm 42 m} 70 := by
  constructor
  · -- Show 70 in the set
    constructor
    · norm_num
    · -- Show that Nat.lcm 15 70 = Nat.lcm 42 70
      native_decide
  · -- Show that 70 is the least
    intro m hm
    rcases hm with ⟨hm_pos, hm_eq⟩
    by_contra h
    push_neg at h
    interval_cases m <;> norm_num [Nat.lcm] at hm_eq