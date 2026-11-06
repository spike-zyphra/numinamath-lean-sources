import Mathlib

theorem number_theory_4977 : IsLeast {n | n ∈ Finset.Icc 10000 99999 ∧ n ≡ 5 [ZMOD 15]} 10010 := by
  constructor
  · -- Show 10010 is in the set
    constructor
    · -- Show 10010 is in the range [10000, 99999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 10010 ≡ 5 [ZMOD 15]
      norm_num [Int.ModEq]
  · -- Show 10010 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    -- Now n < 10010
    have h3 : n < 10010 := by linarith
    interval_cases n <;> norm_num [Int.ModEq] at hn2 <;> omega