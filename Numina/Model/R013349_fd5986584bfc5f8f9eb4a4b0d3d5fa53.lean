import Mathlib

theorem number_theory_228088 :
    IsLeast {k | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m < n ∧ (1978 ^ m) % 1000 = (1978 ^ n) % 1000 ∧ k = m + n} 106 := by
  constructor
  · -- Show that 106 is in the set
    use 3, 103
    all_goals
      norm_num
  · -- Show that 106 is the smallest element in the set
    intro k hk
    rcases hk with ⟨m, n, hm1, hn1, hm2, heq, hk⟩
    by_contra h
    push_neg at h
    have hk' : k < 106 := by nlinarith
    have h1 : m + n < 106 := by nlinarith [hk, hk']
    have h2 : m ≤ 52 := by 
      omega 
    have h3 : n ≤ 105 := by
      omega 
    interval_cases m <;> interval_cases n <;> norm_num [hk] at heq ⊢ 
    <;> omega