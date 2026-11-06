import Mathlib

theorem number_theory_96658 : IsLeast {k : ℕ | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ 75 * m = n ^ 3 ∧ m + n = k} 60 := by
  constructor
  · -- Show 60 is achievable via m = 45 and n = 15
    use 45, 15
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro k hk
    rcases hk with ⟨m, n, hm, hn, h_eq, hk⟩
    by_contra h
    push_neg at h
    have h1 : m + n < 60 := by linarith
    have h2 : m < 60 := by omega
    have h3 : n < 60 := by omega
    interval_cases n <;> omega