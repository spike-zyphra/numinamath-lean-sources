import Mathlib

theorem number_theory_258653 :
    IsLeast {k | ∃ m n, m > 0 ∧ n > 0 ∧ m < n ∧ (1978 ^ m) % 1000 = (1978 ^ n) % 1000 ∧ k = m + n} 106 := by 
  constructor
  · -- Show that 106 is in the set 
    use 3, 103 
    all_goals norm_num 
  · -- Show that any element in the set is at least 106
    intro k hk 
    rcases hk with ⟨m, n, hm, hn, hmn, heq, hk⟩ 
    by_contra h 
    push_neg at h 
    have h1 : m + n < 106 := by 
      omega 
    have h2 : m ≤ 103 := by 
      by_contra h4 
      push_neg at h4 
      have h3 : m ≥ 104 := by 
        omega 
      have h4 : n > 104 := by 
        omega 
      have h5 : m + n ≥ 209 := by 
        omega 
      omega 
    have h3 : n ≤ 104 := by 
      omega 
    have h4 : m ≤ 52 := by 
      omega 
    interval_cases m <;> try { 
      omega 
    } <;> norm_num at heq ⊢ 
      <;> try { 
      interval_cases n 
        <;> omega 
      }