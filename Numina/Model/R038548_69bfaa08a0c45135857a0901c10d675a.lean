import Mathlib

theorem number_theory_134938 :
    IsLeast {n | n ∈ Finset.Icc 1000 9999 ∧ 1111 ∣ n + (n / 100) * (n % 100)} 1729 := by
  constructor
  · -- Show that 1729 is in the set
    constructor
    · -- Show that 1729 ∈ [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that 1111 divides 1729 + (1729 / 100) * (1729 % 100)
      norm_num
  · -- Show that 1729 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 <;> omega