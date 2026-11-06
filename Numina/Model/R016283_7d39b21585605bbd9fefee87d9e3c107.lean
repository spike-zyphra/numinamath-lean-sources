import Mathlib

theorem number_theory_7070 :
    IsLeast {k | ∃ n m : ℕ, n > 0 ∧ m > 0 ∧ m < n ∧ (1978 ^ m) % 1000 = (1978 ^ n) % 1000 ∧ k = n + m} 106 := by 
  constructor
  · -- Show that 106 is in the set
    use 103, 3
    all_goals
      norm_num
  · -- Show that 106 is minimal
    intro k hk
    rcases hk with ⟨n, m, hn, hm, hmn, heq, hk⟩
    by_contra h
    push_neg at h
    have h1 : n + m < 106 := by
      linarith [h, hk]
    have h2 : n ≤ 104 := by 
      omega
    have h3 : m ≤ 53 := by
      omega
    interval_cases n <;> interval_cases m 
      <;> norm_num [Nat.pow_mod] at heq 
      <;> omega