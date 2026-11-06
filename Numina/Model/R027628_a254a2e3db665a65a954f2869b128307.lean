import Mathlib

theorem number_theory_195359 (A B C : ℕ) (h₀ : (Nat.digits 10 A).sum = B)
    (h₁ : (Nat.digits 10 B).sum = C) (h₂ : A + B + C = 60) :
    A = 44 ∨ A = 47 ∨ A = 50 := by
  have h3 : A ≤ 60 := by 
    omega
  have h4 : B ≤ 60 := by
    omega
  interval_cases A <;> norm_num at h₀ h₂
    <;> try { 
      have h4 : B ≤ 60 := by 
        omega 
      interval_cases B <;> norm_num at h₀ h₁ h₂ 
        <;> omega 
    }
    <;> try { 
      simp_all [Nat.digits, Nat.digitsAux]
      <;> try { 
        omega 
      }
      <;> try { 
        tauto 
      }
    }
    <;> try { 
      omega 
    }