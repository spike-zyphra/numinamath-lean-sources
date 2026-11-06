import Mathlib

theorem number_theory_312229 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : (n / 1000) % 10 ^ 2 + (n % 1000) % 10 ^ 2 = 13)
    (h₂ : (n / 100) % 10 ^ 2 + (n % 100) % 10 ^ 2 = 85) (h₃ : ∃ m, m ∈ Finset.Icc 1000 9999 ∧ n - 1089 = m ∧
    (m / 1000) % 10 ^ 2 + (m % 1000) % 10 ^ 2 = 13 ∧ (m / 100) % 10 ^ 2 + (m % 100) % 10 ^ 2 = 85) :
    n = 3762 := by 
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₄, h₅⟩ 
  rcases h₃ with ⟨m, hm1, h_eq1, h_eq2, h_eq3⟩ 
  rw [Finset.mem_Icc] at hm1 
  rcases hm1 with ⟨hm2, hm3⟩ 
  have h6 : n = m + 1089 := by 
    omega 
  have h7 : n / 1000 < 10 := by 
    omega 
  have h8 : (n / 1000) % 10 = n / 1000 := by
    omega 
  have h9 : (n % 1000) % 10 = n % 10 := by 
    omega 
  have h11 : n % 100 % 10 = n % 10 := by 
    omega 
  simp [h8, h9] at h₁ 
  simp [h11] at h₂ 
  have eq1 : (n / 100) % 10 < 10 := by 
    omega 
  interval_cases h : n / 1000 <;> try { 
    omega 
  } <;> try { 
    have : n % 10 ≤ 9 := by 
      omega 
    interval_cases h' : n % 10 
    <;> norm_num at h₁ h₂ 
    <;> try { 
      omega 
    } 
  }