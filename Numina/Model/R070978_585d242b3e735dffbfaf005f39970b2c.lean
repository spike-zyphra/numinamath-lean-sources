import Mathlib

theorem algebra_7065 (a b c d : ℤ) (h₀ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (h₁ : a = 2 ∨ a = 4 ∨ a = 6 ∨ a = 8) (h₂ : b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 8)
    (h₃ : c = 2 ∨ c = 4 ∨ c = 6 ∨ c = 8) (h₄ : d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8) :
    a * b + b * c + b * d + c * d ≤ 120 := by
  rcases h₁ with (r₁ | r₁ | r₁ | r₁) <;> rcases h₂ with (r₂ | r₂ | r₂ | r₂) <;> rcases h₃ with (r₃ | r₃ | r₃ | r₃) <;> rcases h₄ with (r₄ | r₄ | r₄ | r₄) <;> 
    try { 
      simp only [r₁, r₂, r₃, r₄] at *
      all_goals 
        omega
    }
  <;> try { 
    omega
  }
  <;> try { 
    tauto
  }
  <;> try { 
    tauto
  }
  <;> try { 
    tauto
  }
  <;> try { 
    tauto
  }