import Mathlib

theorem number_theory_112644 : IsGreatest {n | n ∈ Finset.Icc 10 99 ∧ 6 ∣ n ∧ (n % 10) = 4} 84 := by
  constructor
  · -- Show that 84 is in the set
    constructor
    · -- Show 84 is in the range [10, 99]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 6 divides 84
      norm_num
    · -- Show 84 % 10 = 4
      norm_num
  · -- Show that no number greater than 84 is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    have h1 : 10 ≤ n := hn1.1
    have h2 : n ≤ 99 := hn1.2
    by_contra h
    push_neg at h
    have h3 : n > 84 := by linarith
    have h4 : n < 100 := by linarith
    have h5 : n = 94 := by
      interval_cases n <;> omega
    rw [h5] at hn2 hn3
    all_goals
      omega