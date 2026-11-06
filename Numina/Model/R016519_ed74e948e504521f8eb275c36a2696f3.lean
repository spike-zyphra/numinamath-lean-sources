import Mathlib

theorem number_theory_81761 : IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c + b * c + c = 2014 ∧ x = a + b + c} 40 := by 
  constructor
  · -- Show that 40 can be obtained.
    use 14, 7, 19
    all_goals 
      norm_num 
  · -- Show that no smaller value can be obtained.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, heq, hx⟩ 
    by_contra h
    push_neg at h
    have h1 : a + b + c < 40 := by 
      linarith [hx, h]
    have h2 : a ≤ 37 := by 
      omega 
    have h3 : b ≤ 37 := by 
      omega 
    have h4 : c ≤ 37 := by 
      omega 
    interval_cases a <;> interval_cases b <;> omega