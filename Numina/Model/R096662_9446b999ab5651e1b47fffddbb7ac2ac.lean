import Mathlib

theorem number_theory_4534 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ n % 13 = 1 ∧ n % 17 = 2 ∧ n % 19 = 3} 8230 := by
  constructor
  · -- Show that 8230 is in the set
    constructor
    · -- Show that 8230 in the range [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- 8230 % 13 = 1
      norm_num
    constructor
    · -- 8230 % 17 = 2
      norm_num
    · -- 8230 % 19 = 3
      norm_num
  · -- Show that 8230 is the greatest
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    -- n > 8230 and n ≤ 9999, so n in (8230, 9999]
    interval_cases n <;> try { omega }
    <;> try { contradiction }
    <;> omega