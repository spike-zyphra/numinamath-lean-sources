import Mathlib

theorem algebra_108757 {a b c : ℝ} (ha : a > 0) (h1 : |a + b + c| = 1) (h2 : |4*a + 2*b + c| = 1)
    (h3 : |9*a + 3*b + c| = 1) :
    (a = 2 ∧ b = -8 ∧ c = 7) ∨ (a = 1 ∧ b = -3 ∧ c = 1) ∨ (a = 1 ∧ b = -5 ∧ c = 5) := by 
  cases' abs_cases (a + b + c) with h11 h11 <;> 
  cases' abs_cases (4*a + 2*b + c) with h22 h22 <;> 
  cases' abs_cases (9*a + 3*b + c) with h33 h33 <;> 
    try { 
      have h4 : a = 2 := by linarith 
      have h5 : b = -8 := by linarith 
      have h6 : c = 7 := by linarith 
      left 
      exact ⟨h4, h5, h6⟩ 
    } 
    <;> 
      try { 
        have h4 : a = 1 := by linarith 
        have h5 : b = -3 := by linarith 
        have h6 : c = 1 := by linarith 
        right 
        left 
        exact ⟨h4, h5, h6⟩ 
      } 
      <;> 
        try { 
          have h4 : a = 1 := by linarith 
          have h5 : b = -5 := by linarith 
          have h6 : c = 5 := by linarith 
          right 
          right 
          exact ⟨h4, h5, h6⟩ 
        } 
        <;> 
          try { 
            linarith 
          }