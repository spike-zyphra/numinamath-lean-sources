import Mathlib

theorem number_theory_209743 : IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ n % 13 = 2 ∧ n % 15 = 6} 951 := by
  constructor
  · -- Show 951 is in the set
    constructor
    · -- Show 951 is in the range [100, 999]
      simp [Finset.mem_Icc]
    constructor
    · -- Show 951 % 13 = 2
      norm_num
    · -- Show 951 % 15 = 6
      norm_num
  · -- Show it's the greatest
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn4, hn5⟩
    by_contra h
    push_neg at h
    -- Assume n > 951, with n % 13 = 2 and n % 15 = 6
    -- But n ≤ 999
    interval_cases n <;> omega
    all_goals
      omega
    all_goals
      omega