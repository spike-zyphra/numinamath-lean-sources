import Mathlib

theorem number_theory_7805 (A B C : ℕ) (h₀ : 0 < A) (h₁ : 0 < B) (h₂ : 0 < C)
    (h₃ : A ≤ 2 * B) (h₄ : B = C - 7) (h₅ : Prime (A + B + C)) (h₆ : A + B + C < 70)
    (h₇ : (Nat.digits 10 (A + B + C)).sum = 13) :
    A ≤ 30 := by

  have h8 : C = B + 7 := by 
    omega 
  have h9 : A + B + C = A + 2 * B + 7 := by 
    rw [h8]
    all_goals 
    omega
  have h4 : A + B + C < 70 := h₆ 
  have h4' : A + B + C ≥ 2 := by 
    omega 
  have h14 : A + B + C ≤ 69 := by 
    omega 
  interval_cases h : A + B + C <;> norm_num at h₅ h₇ h9 ⊢ 
  <;> try { 
    omega 
  }
  <;> try { 
    exfalso 
    <;> try { 
      contradiction 
    } 
  }
  all_goals 
  try { 
    tauto 
  }