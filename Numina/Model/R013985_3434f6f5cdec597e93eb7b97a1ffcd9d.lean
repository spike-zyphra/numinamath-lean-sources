import Mathlib

theorem algebra_16166 {n : ℤ} (h₀ : 4 ∣ n) (h₁ : (n % 100) / 10 + (n % 10) = 13) :
    (n % 100) / 10 * (n % 10) = 42 := by
  have h2 : n % 4 = 0 := by 
    omega
  have h3 : n % 100 % 10 = n % 10 := by 
    omega 
  have h4 : (n % 100) / 10 + (n % 10) = 13 := h₁
  have h5 : n % 4 = 0 := h2
  have h6 : (n % 100) / 10 * (n % 10) = 42 := by
    have h7 : n % 100 ≥ 0 := by 
      omega
    have h8 : n % 100 < 100 := by 
      omega
    interval_cases h : n % 100 <;> omega 
    <;> try { 
      omega 
    }
    <;> try { 
      interval_cases h' : n % 100 <;> try { 
        omega 
      }
    }
  exact h6