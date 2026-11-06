import Mathlib

theorem number_theory_191371 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (n % 10) = 3 * (n / 100)) (h₂ : n % 5 = 4) (h₃ : n % 11 = 3) :
    n = 399 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ <;> omega