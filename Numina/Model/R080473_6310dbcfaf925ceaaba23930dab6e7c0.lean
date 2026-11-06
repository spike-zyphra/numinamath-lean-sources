import Mathlib

theorem number_theory_131409 : IsLeast {n : ℕ | 0 < n ∧ 2019 ∣ (n^2 + 20 * n + 19)} 2000 := by 
  constructor 
  · -- Show that 2000 is in the set.
    constructor
    · norm_num
    · norm_num
  · -- Now, we need to show that 2000 is minimal: if n ∈ {n : ℕ | 0 < n ∧ 2019 ∣ (n^2 + 20 * n + 19)}, then n ≥ 2000
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_div <;> all_goals omega