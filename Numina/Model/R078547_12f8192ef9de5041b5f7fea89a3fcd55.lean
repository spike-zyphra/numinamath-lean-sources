import Mathlib

theorem number_theory_110547 :
    IsLeast {n | 0 < n ∧ (n^2) % 1000 = 111 ∨ (n^2) % 1000 = 222 ∨ (n^2) % 1000 = 333 ∨ (n^2) % 1000 = 444 ∨ (n^2) % 1000 = 555 ∨ (n^2) % 1000 = 666 ∨ (n^2) % 1000 = 777 ∨ (n^2) % 1000 = 888 ∨ (n^2) % 1000 = 999} 38 := by
  constructor
  · -- Show that 38 is in this set
    simp
    all_goals norm_num
  · -- Show that 38 is the smallest element in the set
    intro n hn
    simp at hn
    rcases hn with (h | h | h | h | h | h | h | h | h)
    · -- Case n > 0 and n^2 % 1000 = 111
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 222
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 333
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 444
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 555
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 666
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 777
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 888
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega
    · -- Case n^2 % 1000 = 999
      by_contra h1
      push_neg at h1
      have h1 : n < 38 := by linarith
      interval_cases n <;> norm_num at h <;> omega