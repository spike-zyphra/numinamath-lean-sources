import Mathlib

theorem number_theory_150003 : IsLeast {n | 0 < n ∧ n % 3 = 1 ∧ n % 4 = 2 ∧ n % 5 = 3} 58 ∧
    IsLeast {n | 0 < n ∧ n % 5 = 1 ∧ n % 6 = 2 ∧ n % 7 = 3} 206 ∧
    IsLeast {n | 0 < n ∧ n % 7 = 1 ∧ n % 8 = 2 ∧ n % 9 = 3} 498 := by
  constructor
  · -- 58 is the least in the first set
    constructor
    · -- Show 58 is in the first set
      show 0 < 58 ∧ 58 % 3 = 1 ∧ 58 % 4 = 2 ∧ 58 % 5 = 3
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    · -- Show no smaller element is in the first set
      intro n hn
      have ⟨hn_pos, hn1, hn2, hn3⟩ := hn
      omega
  constructor
  · -- 206 is the least in the second set
    constructor
    · -- Show 206 is in the second set
      show 0 < 206 ∧ 206 % 5 = 1 ∧ 206 % 6 = 2 ∧ 206 % 7 = 3
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    · -- Show no smaller element is in the second set
      intro n hn
      have ⟨hn_pos, hn1, hn2, hn3⟩ := hn
      omega
  · -- 498 is the least in the third set
    constructor
    · -- Show 498 is in the third set
      show 0 < 498 ∧ 498 % 7 = 1 ∧ 498 % 8 = 2 ∧ 498 % 9 = 3
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    · -- Show no smaller element is in the third set
      intro n hn
      have ⟨hn_pos, hn1, hn2, hn3⟩ := hn
      omega