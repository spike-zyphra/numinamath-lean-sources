import Mathlib

theorem number_theory_19547 :
    IsLeast {r : ℕ | 1000 ≤ r ∧ r ≤ 9999 ∧ r^2 + 4 * r + 4 ≡ r^2 + 2 * r + 1 [MOD 55]} 1016 := by
  constructor
  · -- Show 1016 is in the set.
    constructor
    · norm_num -- Show that 1000 ≤ 1016
    constructor
    · norm_num -- Show that 1016 ≤ 9999
    · norm_num [Nat.ModEq]
  · -- Show that 1016 is the least in the set
    intro r hr
    rcases hr with ⟨hr1000, hr9999, hcong⟩
    by_contra h
    push_neg at h
    interval_cases r <;> norm_num [Nat.ModEq] at hcong
    all_goals omega