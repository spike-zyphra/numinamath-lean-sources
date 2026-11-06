import Mathlib

theorem number_theory_120921 :
    IsLeast {n | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).length = 5 ∧ (Nat.digits 10 n).toFinset.card = 5 ∧ 9 ∣ n ∧ 4 ∣ (n / 10)} 10287 := by
  constructor
  · -- Show that 10287 is in the set
    constructor
    · -- Show that 10287 is in the range [10000, 99999]
      native_decide
    constructor
    · -- Show it has five digits
      native_decide
    constructor
    · -- Show all digits are unique
      native_decide
    constructor
    · -- Show divisibility by 9
      omega
    · -- Show divisibility by 4 of the first four digits
      omega
  · -- Show that 10287 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4, hn5⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1a, hn1b⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn4 hn5 hn2 hn3 <;> all_goals try { contradiction }
    all_goals try { omega }
    all_goals try { native_decide }