import Mathlib

theorem algebra_108765 {a b c : ℝ} (ha : a > 0) (h1 : |a + b + c| = 2)
    (h2 : |4*a + 2*b + c| = 2) (h3 : |9*a + 3*b + c| = 2) :
    (a = 4 ∧ b = -16 ∧ c = 14) ∨ (a = 2 ∧ b = -6 ∧ c = 2) ∨
    (a = 2 ∧ b = -10 ∧ c = 10) := by
  cases' abs_cases (a + b + c) with h1' h1' <;> cases' abs_cases (4*a + 2*b + c) with h2' h2' <;> cases' abs_cases (9*a + 3*b + c) with h3' h3' <;> 
    try { 
      have h4 : a = 4 := by 
        nlinarith
      have h5 : b = -16 := by 
        nlinarith
      have h6 : c = 14 := by 
        nlinarith
      left 
      exact ⟨h4, h5, h6⟩ 
    } <;> 
      try { 
        have h4 : a = 2 := by 
          nlinarith
        have h5 : b = -6 := by 
          nlinarith
        have h6 : c = 2 := by 
          nlinarith
        right
        left
        exact ⟨h4, h5, h6⟩ 
      } <;> 
        try { 
          have h4 : a = 2 := by 
            nlinarith
          have h5 : b = -10 := by 
            nlinarith
          have h6 : c = 10 := by 
            nlinarith
          right
          right 
          exact ⟨h4, h5, h6⟩ 
        } <;> 
          try { 
            nlinarith 
          }