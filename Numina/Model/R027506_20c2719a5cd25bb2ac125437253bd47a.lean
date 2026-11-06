import Mathlib

theorem number_theory_97324 (n : ℕ) (hn : n = 126) :
    IsGreatest {x | ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = n ∧ x = p - q} 100 := by 
  rw [hn]
  constructor
  · -- Show that 100 is in the set.
    use 113, 13
    all_goals
    norm_num
  · -- Show that 100 is greatest.
    intro x hx
    rcases hx with ⟨p, q, hp, hq, hneq, heq, hx⟩
    by_contra h
    push_neg at h
    have h1 : p + q = 126 := heq
    have h4 : q < 13 := by
      omega
    have h5 : q ≤ 11 := by 
      by_contra h6 
      push_neg at h6 
      have h7 : q = 12 := by 
        omega 
      rw [h7] at hq 
      norm_num at hq 
    interval_cases q <;> norm_num at hq 
    <;> try { 
      omega
    }
    all_goals
      try { 
        have h2 : p ≤ 126 := by 
          omega 
        interval_cases p <;> norm_num at hp heq <;> all_goals omega 
      }