import Mathlib

theorem number_theory_93914 : IsLeast {d | ∃ a, a * (a + d) = 1998} 17 := by 
  constructor
  · -- Show that 17 is achievable
    use 37
    all_goals norm_num
  · -- Show that 17 is the least such
    intro d
    intro h
    rcases h with ⟨a, ha⟩
    
    by_contra h'
    push_neg at h'
    
    have h1 : d < 17 := by linarith
    have h2 : a ≤ 44 := by
      by_contra h3
      push_neg at h3
      nlinarith [sq_nonneg (a + d), sq_nonneg (a), show d ≥ 0 by linarith, h1, show a > 0 by nlinarith, show a + d > 0 by nlinarith]
    
    interval_cases a <;> omega