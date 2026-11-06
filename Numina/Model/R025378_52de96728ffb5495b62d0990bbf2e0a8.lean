import Mathlib

theorem algebra_108773 (a b c : ℝ) (ha : a > 0) (h1 : |a + b + c| = 3) (h2 : |4*a + 2*b + c| = 3)
    (h3 : |9*a + 3*b + c| = 3) :
    (a = 6 ∧ b = -24 ∧ c = 21) ∨ (a = 3 ∧ b = -15 ∧ c = 15) ∨
    (a = 3 ∧ b = -9 ∧ c = 3) := by
  cases' abs_cases (a + b + c) with h11 h11 <;> 
  cases' abs_cases (4*a + 2*b + c) with h22 h22 <;> 
  cases' abs_cases (9*a + 3*b + c) with h33 h33 <;> 
  try { 
    have h4 : a = 6 := by 
      nlinarith 
    have h5 : b = -24 := by 
      nlinarith 
    have h6 : c = 21 := by 
      nlinarith 
    left 
    exact ⟨h4, h5, h6⟩ 
  }
  try { 
    have h4 : a = 3 := by 
      nlinarith 
    have h5 : b = -15 := by 
      nlinarith 
    have h6 : c = 15 := by 
      nlinarith 
    right 
    left 
    exact ⟨h4, h5, h6⟩ 
  }
  try { 
    have h4 : a = 3 := by 
      nlinarith 
    have h5 : b = -9 := by 
      nlinarith 
    have h6 : c = 3 := by 
      nlinarith 
    right 
    right 
    exact ⟨h4, h5, h6⟩ 
  }
  try { 
    nlinarith 
  }