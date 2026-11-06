import Mathlib

theorem inequalities_13557 :
    IsLeast {n | 0 < n ∧ n ^ 240 ≥ 13 ^ 320} 31 := by
  constructor
  · -- First, we'll verify 31 is in the set
    constructor
    · norm_num
    · -- Show that 31^240 ≥ 13^320
      norm_num
  · -- Now, we need to prove minimal
    intro n hn
    rcases hn with ⟨hn_pos, hn_ineq⟩
    by_contra h
    push_neg at h
    -- n <31
    have h1 : n ≤ 30 := by 
      omega
    -- If n ≤30, then n^240 <13^320
    have h2 : n ^ 240 < (13 : ℕ) ^ 320 := by
      interval_cases n <;> norm_num
      all_goals
        omega
    -- This contradicts with the hypothesis n^240 ≥13^320
    omega