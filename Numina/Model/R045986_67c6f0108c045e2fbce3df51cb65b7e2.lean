import Mathlib

theorem number_theory_308578 :
    IsLeast {x | ∃ a b c : ℕ, 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ 9 ∧ x = a + b + c ∧ 9 ∣ (100 * a + 10 * b + c) * (100 * b + 10 * c + a) * (100 * c + 10 * a + b) + 1} 8 ∧
    IsGreatest {x | ∃ a b c : ℕ, 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ 9 ∧ x = a + b + c ∧ 9 ∣ (100 * a + 10 * b + c) * (100 * b + 10 * c + a) * (100 * c + 10 * a + b) + 1} 23 := by
  constructor
  · 
    constructor
    · -- Show that 8 is in the set
      use 1, 2, 5
      norm_num
    · -- Show that 8 is minimal
      intro x h
      rcases h with ⟨a, b, c, h1, h2, h3, h4, h5, h6⟩
      have h7 : a ≤ 9 := by linarith
      have h8 : b ≤ 9 := by 
        have h3' : b < c := h3
        omega
      have h9 : c ≤ 9 := by linarith 
      by_contra h'
      push_neg at h'
      have : x < 8 := by linarith
      have h10 : a + b + c < 8 := by linarith [h5, this]
      interval_cases a <;> interval_cases b <;> interval_cases c <;> omega
  · -- Show that 23 is greatest 
    constructor
    · -- Show that 23 is in the set
      use 6, 8, 9
      norm_num
    · -- Show that 23 is greatest
      intro x h
      rcases h with ⟨a, b, c, h1, h2, h3, h4, h5, h6⟩
      have h7 : a ≤ 9 := by linarith 
      have h8 : b ≤ 9 := by 
        have h3' : b < c := h3
        omega 
      have h9 : c ≤ 9 := by linarith 
      by_contra h'
      push_neg at h'
      have : x > 23 := by linarith 
      have h10 : a + b + c > 23 := by linarith [h5, this] 
      have h11 : a + b + c ≤ 24 := by
        have h12 : c ≤ 9 := by linarith 
        have h13 : b ≤ 8 := by 
          omega 
        have h14 : a ≤ 7 := by 
          omega 
        linarith 
      interval_cases a <;> interval_cases b <;> interval_cases c <;> omega