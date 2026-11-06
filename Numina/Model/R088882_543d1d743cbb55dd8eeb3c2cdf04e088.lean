import Mathlib

theorem number_theory_229894 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n / (n % 100) = 9) (h₂ : n % (n % 100) = 8) :
    n = 224 ∨ n = 449 ∨ n = 674 ∨ n = 899 := by 
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₀1, h₀2⟩
  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> omega