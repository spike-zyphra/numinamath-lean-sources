import Mathlib

theorem number_theory_613237:
    let sum (n : ℕ) := ∑ i ∈ Finset.range (n + 1) , i ^ 2
    IsLeast {n | 2 < n ∧ ∃ m, sum n = m^2} 24 :=
by
  constructor
  · -- Show 24 is in the set
    constructor
    · norm_num
    · -- Show that when n = 24, the sum is a perfect square
      use 70
      native_decide
  · -- Show that no smaller n > 2 is in the set
    intro n hn
    rcases hn with ⟨hn2, ⟨m, hm⟩⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 23 := by linarith
    interval_cases n <;> try { 
      norm_num [Finset.sum_range_succ] at hm
      all_goals
        try { 
          have h2 : m ≤ 70 := by nlinarith
          interval_cases m <;> omega
        }
    }