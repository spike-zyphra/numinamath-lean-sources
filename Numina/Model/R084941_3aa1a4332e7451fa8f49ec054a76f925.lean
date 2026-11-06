import Mathlib

theorem number_theory_6142 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ Nat.gcd n 4734 = 263} 9731 := by
  constructor
  · -- Show that 9731 is in the set
    constructor
    · -- Show that 9731 is in the range [1000, 9999]
      simp [Finset.mem_Icc]
    · -- Show that gcd(9731, 4734) = 263
      norm_num [Nat.gcd]
  · -- Show that 9731 is greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn3, hn4⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hn2 <;> all_goals omega