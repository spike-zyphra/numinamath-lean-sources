import Mathlib

theorem number_theory_15030 :
    IsLeast {n : ℕ | 0 < n ∧ Nat.gcd (9 * n - 2) (7 * n + 3) > 1} 23 := by
  constructor
  · -- Show that 23 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that it's the least
    intro n hn
    rcases hn with ⟨hn_pos, hn_gcd⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_gcd <;> all_goals contradiction