import Mathlib

theorem number_theory_23333 (r : ℕ) (hr : r = 1342 % 13) :
    IsLeast {n : ℕ | 0 < n ∧ 1342 ∣ n ∧ n % 13 < r} 6710 := by 
  have hr_val : r = 3 := by
    norm_num [hr]
  constructor
  · -- Show 6710 is in the set
    constructor
    · -- Show 6710 > 0
      norm_num
    constructor
    · -- Show 1342 divides 6710
      norm_num
    · -- Show 6710 % 13 < 3
      norm_num [hr_val]
  · -- Show 6710 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_mod⟩
    by_contra h
    push_neg at h
    have h1 : n % 1342 = 0 := by
      omega
    have h2 : ∃ k : ℕ, n = 1342 * k := by
      refine ⟨n / 1342, by omega⟩
    rcases h2 with ⟨k, hk⟩
    have hk_lt : 1342 * k < 6710 := by
      linarith [h, hk]
    have hk_pos : k > 0 := by
      by_contra h
      push_neg at h
      have : k = 0 := by linarith
      rw [this] at hk
      nlinarith
    have h3 : k < 5 := by
      nlinarith [hk_lt]
    have hk1 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      omega
    rcases hk1 with (rfl | rfl | rfl | rfl)
    · -- k = 1
      norm_num [hr_val] at hn_mod
      all_goals
      omega
    · -- k = 2
      norm_num [hr_val] at hn_mod
      all_goals
      omega
    · -- k = 3
      norm_num [hr_val] at hn_mod
      all_goals
      omega
    · -- k = 4
      norm_num [hr_val] at hn_mod
      all_goals
      omega