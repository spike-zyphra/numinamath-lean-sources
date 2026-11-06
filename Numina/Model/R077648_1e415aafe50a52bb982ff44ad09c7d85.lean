import Mathlib

theorem number_theory_263282 :
    IsLeast {n | n ∈ Finset.Icc 100 999 ∧ Odd (n / 100) ∧ 3 ∣ n} 102 := by
  constructor
  · -- We check that 102 is in the set
    constructor
    · -- Show 102 is in the range [100, 999]
      simp [Finset.mem_Icc]
    constructor
    · -- Show that 1 (the hundreds digit of 102) is odd
      decide
    · -- Show that 102 is divisible by 3
      norm_num
  · -- Now we prove that 102 is the smallest such number
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.odd_iff] at hn2 hn3 <;> all_goals contradiction