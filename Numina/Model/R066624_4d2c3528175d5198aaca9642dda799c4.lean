import Mathlib

theorem number_theory_159509 :
    IsLeast {k | ∃ m n : ℕ, m > n ∧ (4 ^ m + 4 ^ n) % 100 = 0 ∧ k = m + n} 7 := by 
  constructor
  · -- Show 7 is in the set
    use 6, 1
    all_goals norm_num
  · -- Show 7 is the minimum
    intro k hk
    rcases hk with ⟨m, n, hmn, hdiv, hk⟩
    by_contra h'
    push_neg at h'
    have h' : k < 7 := by linarith
    have h1 : m + n < 7 := by
      linarith [hk, h']
    -- So m + n < 7
    -- Therefore, m < 7, n < 7. Let's check all possible combinations
    have h2 : m ≤ 6 := by 
      omega
    have h3 : n ≤ 6 := by 
      omega
    interval_cases m <;> interval_cases n <;> omega