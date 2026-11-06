import Mathlib

theorem number_theory_4498 : IsLeast {n | n > 38 ∧ ¬∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = n^2} 42 := by 
  constructor 
  · -- First, show 42 is in the set.
    constructor 
    · -- Show 42 > 38
      norm_num
    · -- Show there do not exist a, b > 0 such that a^2 + b^2 = 42^2
      intro h 
      rcases h with ⟨a, b, ha, hb, heq⟩ 
      have h1 : a ≤ 42 := by 
        nlinarith 
      have h2 : b ≤ 42 := by 
        nlinarith 
      interval_cases a <;> try { 
        interval_cases b <;> omega 
      }
  · -- Show that 42 is the least such
    intro n hn 
    rcases hn with ⟨hn1, hn2⟩ 
    by_contra h 
    push_neg at h 
    have h2 : n = 39 ∨ n = 40 ∨ n = 41 := by 
      omega 
    rcases h2 with (r | r | r) 
    · -- Assume n = 39 
      rw [r] at hn2 
      have h3 : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = (39 : ℕ) ^2 := by 
        use 36, 15 
        all_goals norm_num 
      contradiction 
    · -- Assume n = 40 
      rw [r] at hn2 
      have h4 : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = (40 : ℕ) ^2 := by 
        use 32, 24 
        all_goals norm_num 
      contradiction 
    · -- Assume n = 41 
      rw [r] at hn2 
      have h5 : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = (41 : ℕ) ^2 := by 
        use 40, 9 
        all_goals norm_num 
      contradiction