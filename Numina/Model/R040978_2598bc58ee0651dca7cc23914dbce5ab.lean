import Mathlib

theorem number_theory_6111 :
    IsLeast {k | ∃ m n, m > n ∧ n ≥ 1 ∧ k = m + n ∧ 1000 ∣ 1978^m - 1978^n} 106 := by
  constructor
  · -- Show 106 is in the set
    use 103, 3
    all_goals norm_num
  · -- Show no element less than 106 is in the set
    intro k hk
    rcases hk with ⟨m, n, h1, h2, hk, h3⟩
    by_contra h
    push_neg at h
    have h4 : m + n < 106 := by 
      linarith
    have h5 : m < 106 := by 
      omega
    have h6 : n < 105 := by 
      omega
    interval_cases n <;> try { 
      omega 
    } <;> try { 
      interval_cases m <;> omega 
    }