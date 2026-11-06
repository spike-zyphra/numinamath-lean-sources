import Mathlib

theorem number_theory_2208 :
    IsLeast {n | n ∈ Finset.Icc 10000 99999 ∧ 9 ∣ n ∧ 4 ∣ (n / 10)} 10008 := by
  constructor
  · -- Show that 10008 is in the set
    constructor
    · -- Show that 10008 is in the range [10000, 99999]
      native_decide
    constructor
    · -- 9 divides 10008
      norm_num
    · -- 4 divides 10008 / 10 (which is 1000)
      norm_num
  · -- Show that 10008 is the minimum element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    have h1 : 10000 ≤ n := hn1.1
    have h2 : n ≤ 99999 := hn1.2
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 hn3 <;> all_goals omega