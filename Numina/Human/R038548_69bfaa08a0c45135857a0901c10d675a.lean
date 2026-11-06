import Mathlib

theorem number_theory_134938 :
    IsLeast {n | n ∈ Finset.Icc 1000 9999 ∧ 1111 ∣ n + (n / 100) * (n % 100)} 1729 := by
  constructor
  · -- Verify 1729 is in the set
    constructor
    · -- Show 1729 ∈ [1000, 9999]
      norm_num
    · -- Show 1111 ∣ 1729 + (1729 / 100) * (1729 % 100)
      norm_num
  · -- Prove that 1729 is the least such number.
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    have h1 : 1000 ≤ n := hn1.1
    have h2 : n ≤ 9999 := hn1.2
    by_contra h
    push_neg at h
    have : n ≤ 1728 := by linarith
    interval_cases n <;> norm_num at *