import Mathlib

theorem number_theory_5431 : IsLeast {a : ℕ | 0 < a ∧ (5 * a ≡ 1 [MOD 11])} 9 := by 
  constructor
  · -- Show that 9 is in the set
    constructor
    · norm_num  -- 9 > 0
    · -- Verify that 5 * 9 ≡ 1 [MOD 11]
      norm_num [Nat.ModEq]
  · -- Show that 9 is indeed the smallest element in the set
    intro a h
    rcases h with ⟨ha_pos, hcong⟩
    by_contra h
    push_neg at h
    interval_cases a <;> norm_num [Nat.ModEq] at hcong <;> all_goals omega