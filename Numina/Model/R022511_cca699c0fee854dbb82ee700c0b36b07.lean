import Mathlib

theorem number_theory_131993 (a b c d : ℕ) (h₀ : a < b ∧ b < c ∧ c < d)
    (h₁ : a * d = 32) (h₂ : b * c = 14) :
    a + b + c + d = 42 := by
  rcases h₀ with ⟨h₀₁, h₀₂, h₀₃⟩
  have h3 : b ≤ 14 := by 
    by_contra h
    push_neg at h
    have h4 : c > 0 := by nlinarith
    have h5 : b * c > 14 := by
      nlinarith [show b > 14 by linarith, show c ≥ 1 by nlinarith]
    omega
  have h4 : c ≤ 14 := by 
    nlinarith [show b ≥ 1 by nlinarith, h₂]
  have h5 : a ≤ 32 := by
    by_contra h
    push_neg at h
    have h6 : d > 0 := by
      nlinarith
    have h7 : a * d > 32 := by
      have ha : a > 32 := by linarith
      have hd : d > 1 := by
        nlinarith
      nlinarith
    omega
  have h8 : d ≤ 32 := by
    by_contra h
    push_neg at h
    have h6 : a > 0 := by
      nlinarith
    have h7 : a * d > 32 := by
      have ha : a > 1 := by
        nlinarith
      have hd : d > 32 := by linarith
      nlinarith
    omega
  interval_cases b <;> try { 
    omega 
  } <;> 
    interval_cases c <;> 
      try { 
        omega 
      }
      <;> 
        interval_cases a <;> 
          try { 
            omega 
          }
          <;> 
            interval_cases d <;> 
              try { 
                all_goals omega 
              }