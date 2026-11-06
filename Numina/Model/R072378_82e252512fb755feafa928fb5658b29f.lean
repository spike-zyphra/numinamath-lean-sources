import Mathlib

theorem number_theory_281531 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (100 + n) + (10 * n + 1) = 728) :
    n = 57 := by 
  have h2 : n ≥ 10 := by 
    simp [Finset.mem_Icc] at h₀ 
    omega 
  have h3 : n ≤ 99 := by 
    simp [Finset.mem_Icc] at h₀ 
    omega 
  omega