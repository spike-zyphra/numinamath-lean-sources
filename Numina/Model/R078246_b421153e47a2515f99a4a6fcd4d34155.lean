import Mathlib

theorem number_theory_7138 :
    IsLeast {a | ∃ b c : ℕ, Odd a ∧ Odd b ∧ b = a + 2 ∧ a + b = c ^ 5} 15 := by
  constructor
  · -- Show 15 is in the set
    use 17, 2
    all_goals decide
  · -- Show no smaller element is in the set
    rintro a ⟨b, c, h1, h2, h3, h4⟩
    by_contra h
    push_neg at h
    have h5 : a < 15 := by linarith
    have h6 : c ≤ 1 := by
      by_contra h'
      push_neg at h'
      have h8 : c ≥ 2 := by linarith
      have h9 : a + b ≥ 32 := by
        have h10 : c ^ 5 ≥ 32 := by
          have : c ^ 5 ≥ 32 := by 
            apply Nat.pow_le_pow_of_le_left h8 5
          linarith
        linarith
      have h10 : a + b < 32 := by 
        omega
      linarith
    interval_cases c <;> try { 
      omega
    }