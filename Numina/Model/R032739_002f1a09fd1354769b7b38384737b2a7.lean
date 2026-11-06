import Mathlib

theorem number_theory_233664 (n m : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : m ∈ Finset.Icc 100 999)
    (h₂ : n % 7 = m % 7) :
    7 ∈ Nat.primeFactors (n * 1000 + m) := by
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h3 : (n * 1000 + m) % 7 = 0 := by
    have h4 : n % 7 = m % 7 := h₂
    omega
  have h4 : 7 ∣ (n * 1000 + m) := by 
    omega
  have h5 : n * 1000 + m > 0 := by 
    omega
  have h6 : 7 ∈ Nat.primeFactors (n * 1000 + m) := by
    rw [Nat.mem_primeFactors]
    constructor
    · -- Show that 7 is prime
      norm_num
    all_goals
      try tauto
      try omega
  exact h6