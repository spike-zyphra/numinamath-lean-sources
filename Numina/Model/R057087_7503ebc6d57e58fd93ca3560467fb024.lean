import Mathlib

theorem number_theory_129251 :
    IsLeast {x | ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ Nat.lcm a b = 240 ∧ x = a + b} 31 := by 
  constructor
  · -- Show that 31 is in the set
    use 15, 16
    all_goals norm_num [Nat.lcm]
  
  · -- Show that 31 is the smallest element in the set
    intro x h
    rcases h with ⟨a, b, ha, hb, h1, h2⟩
    
    by_contra h'
    push_neg at h'
    
    have h3 : a ≤ 30 := by 
      omega

    have h4 : b ≤ 30 := by 
      omega

    interval_cases a <;> interval_cases b
      <;> norm_num [Nat.lcm] at h1 ⊢
      <;> omega